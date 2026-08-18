// See LICENSE.SiFive for license details.

package freechips.rocketchip.tilelink

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.diplomacy._
import freechips.rocketchip.util._
import TLMessages._

case class TLCacheCorkParams(
  unsafe: Boolean = false,
  sinkIds: Int = 20,
  writeBufEntries: Int = 80,
  ram_latency: Int = 100,
  ram_bandiwdth: Int = 10, // 1/bandwidth
  a_queue_depth: Int = 100,
  num_write_beats: Int = 4,
  num_llc_mshrs: Int = 20)

class RSMetadata[T <: Data](sourceField: T) extends Bundle {
  val readValid = Bool()
  val writeValid = Bool()
  val source = sourceField.cloneType
}

class TLRRCacheCork(params: TLCacheCorkParams = TLCacheCorkParams())(implicit p: Parameters) extends LazyModule
{
  val unsafe = params.unsafe
  val sinkIds = params.sinkIds
  val node = TLAdapterNode(
    clientFn  = { case cp =>
      cp.v1copy(clients = cp.clients.map { c => c.v1copy(
        supportsProbe = TransferSizes.none,
        sourceId = IdRange(c.sourceId.start*2, c.sourceId.end*2))})},
    managerFn = { case mp =>
      mp.v1copy(
        endSinkId = if (mp.managers.exists(_.regionType == RegionType.UNCACHED)) sinkIds else 0,
        managers = mp.managers.map { m => m.v1copy(
          supportsAcquireB = if (m.regionType == RegionType.UNCACHED) m.supportsGet     else m.supportsAcquireB,
          supportsAcquireT = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull.intersect(m.supportsGet) else m.supportsAcquireT,
          alwaysGrantsT    = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull else m.alwaysGrantsT)})})

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    (node.in zip node.out) foreach { case ((in, edgeIn), (out, edgeOut)) =>
      // If this adapter does not need to do anything, toss all the above work and just directly connect
      if (!edgeIn.manager.anySupportAcquireB) {
        out <> in
      } else {
        val clients = edgeIn.client.clients
        val caches = clients.filter(_.supports.probe)
        require (clients.size == 1 || caches.size == 0 || unsafe, s"Only one client can safely use a TLCacheCork; ${clients.map(_.name)}")
        require (caches.size <= 1 || unsafe, s"Only one caching client allowed; ${clients.map(_.name)}")
        edgeOut.manager.managers.foreach { case m =>
          require (!m.supportsAcquireB || unsafe, s"Cannot support caches beyond the Cork; ${m.name}")
          require (m.regionType <= RegionType.UNCACHED)
        }

        // The Cork turns [Acquire=>Get] => [AccessAckData=>GrantData]
        //            and [ReleaseData=>PutFullData] => [AccessAck=>ReleaseAck]
        // We need to encode information sufficient to reverse the transformation in output.
        // A caveat is that we get Acquire+Release with the same source and must keep the
        // source unique after transformation onto the A channel.
        // The coding scheme is:
        //   Release, AcquireBlock.BtoT, AcquirePerm => instant response
        //   Put{Full,Partial}Data: 1, ReleaseData: 0 => AccessAck
        //   {Arithmetic,Logical}Data,Get: 0, Acquire: 1 => AccessAckData
        //   Hint:0 => HintAck

        // The CacheCork can potentially send the same source twice if a client sends
        // simultaneous Release and AMO/Get with the same source. It will still correctly
        // decode the messages based on the D.opcode, but the double use violates the spec.
        // Fortunately, no masters we know of behave this way!

        // Take requests from A to A or D (if BtoT Acquire)
        val a_a = Wire(chiselTypeOf(out.a))
        val a_d = Wire(chiselTypeOf(in.d))
        val isPut = in.a.bits.opcode === PutFullData || in.a.bits.opcode === PutPartialData
        val toD = (in.a.bits.opcode === AcquireBlock && in.a.bits.param === TLPermissions.BtoT) ||
                  (in.a.bits.opcode === AcquirePerm)

        // latency implementation
        val a_latency_bits = Wire(chiselTypeOf(out.a.bits))
        val a_latency_valid = Wire(chiselTypeOf(out.a.valid))
        out.a.bits := ShiftRegister(a_latency_bits, params.ram_latency - 4, out.a.ready)
        out.a.valid := ShiftRegister(a_latency_valid, params.ram_latency - 4, out.a.ready)

        a_a.bits := in.a.bits
        a_a.bits.source := in.a.bits.source << 1 | Mux(isPut, 1.U, 0.U)

        // Transform Acquire into Get
        when (in.a.bits.opcode === AcquireBlock || in.a.bits.opcode === AcquirePerm) {
          a_a.bits.opcode := Get
          a_a.bits.param  := 0.U
          a_a.bits.source := in.a.bits.source << 1 | 1.U
        }

        // Upgrades are instantly successful
        a_d.valid := in.a.valid && toD
        a_d.bits := edgeIn.Grant(
          fromSink = 0.U,
          toSource = in.a.bits.source,
          lgSize   = in.a.bits.size,
          capPermissions = TLPermissions.toT)

        // Take ReleaseData from C to A; Release from C to D
        val c_a = Wire(chiselTypeOf(out.a))
        c_a.bits := edgeOut.Put(
          fromSource = in.c.bits.source << 1,
          toAddress  = in.c.bits.address,
          lgSize     = in.c.bits.size,
          data       = in.c.bits.data,
          corrupt    = in.c.bits.corrupt)._2
        c_a.bits.user :<= in.c.bits.user

        // Releases without Data succeed instantly
        val c_d = Wire(chiselTypeOf(in.d))
        c_d.valid := in.c.valid && in.c.bits.opcode === Release
        c_d.bits := edgeIn.ReleaseAck(in.c.bits)
        // Releases that enter the write queue respond early
        val c_a_d = Wire(chiselTypeOf(in.d))
        c_a_d.bits := edgeIn.ReleaseAck(in.c.bits)
        c_a_d.valid := false.B
        dontTouch(c_a_d.valid)

        assert (!in.c.valid || in.c.bits.opcode === Release || in.c.bits.opcode === ReleaseData)
        in.c.ready := Mux(in.c.bits.opcode === Release, c_d.ready, c_a.ready)

        // Discard E
        in.e.ready := true.B

        // Block B; should never happen
        out.b.ready := false.B
        assert (!out.b.valid)

        // Track in-flight sinkIds
        val pool = Module(new IDPool(sinkIds))
        pool.io.free.valid := in.e.fire
        pool.io.free.bits  := in.e.bits.sink

        val in_d = Wire(chiselTypeOf(in.d))
        val d_first = edgeOut.first(in_d)
        val d_grant = in_d.bits.opcode === GrantData || in_d.bits.opcode === Grant
        pool.io.alloc.ready := in.d.fire && d_first && d_grant
        in.d.valid := in_d.valid && (pool.io.alloc.valid || !d_first || !d_grant)
        in_d.ready := in.d.ready && (pool.io.alloc.valid || !d_first || !d_grant)
        in.d.bits := in_d.bits
        in.d.bits.sink := pool.io.alloc.bits holdUnless d_first

        // Take responses from D and transform them
        val d_d = Wire(chiselTypeOf(in.d))
        d_d <> out.d
        d_d.bits.source := out.d.bits.source >> 1

        // Record if a target was writable and auto-promote toT if it was
        // This is structured so that the vector can be constant prop'd away
        val wSourceVec = Reg(Vec(edgeIn.client.endSourceId, Bool()))
        val aWOk = edgeIn.manager.fastProperty(in.a.bits.address, !_.supportsPutFull.none, (b:Boolean) => b.B)
        val dWOk = wSourceVec(d_d.bits.source)
        val bypass = (edgeIn.manager.minLatency == 0).B && in.a.valid && in.a.bits.source === d_d.bits.source
        val dWHeld = Mux(bypass, aWOk, dWOk) holdUnless d_first

        when (in.a.fire) {
          wSourceVec(in.a.bits.source) := aWOk
        }

        // Wipe out any unused registers
        edgeIn.client.unusedSources.foreach { id =>
          wSourceVec(id) := edgeIn.manager.anySupportPutFull.B
        }

        when (out.d.bits.opcode === AccessAckData && out.d.bits.source(0)) {
          d_d.bits.opcode := GrantData
          d_d.bits.param := Mux(dWHeld, TLPermissions.toT, TLPermissions.toB)
        }
        when (out.d.bits.opcode === AccessAck && !out.d.bits.source(0)) {
          //d_d.bits.opcode := ReleaseAck
          // we respond to release when it enters write queue, not here
          d_d.valid := false.B
        }

        // Combine the sources of messages into the channels
        // TLArbiter(TLArbiter.lowestIndexFirst)(out.a, (edgeOut.numBeats1(c_a.bits), c_a), (edgeOut.numBeats1(a_a.bits), a_a))
        a_latency_valid := false.B 
        a_latency_bits := DontCare
        TLArbiter(TLArbiter.lowestIndexFirst)(in_d, (edgeIn.numBeats1(d_d.bits), d_d), (0.U, Queue(c_a_d, 2)), (0.U, Queue(c_d, 2)), (edgeIn.numBeats1(a_d.bits), Queue(a_d, 8)))

        // implement RS per MSHR to accomodate all requests, iterate over them in WCRR order, then also include a write buffer.
        val c_enq = Wire(Bool())
        val c_deq = Wire(Bool())
        c_enq := false.B
        c_deq := false.B

        val rs_valid_vec = RegInit(VecInit(Seq.fill(params.num_llc_mshrs)(0.U.asTypeOf(new RSMetadata(chiselTypeOf(in.a.bits.source >> 1)))))) // a_a = in_a <<1|1.U, c_a = in_c<<1
        // val rs_full = !(rs_valid_vec.map(_.readValid & _.writeValid).andR)
        val rs_empty = !(rs_valid_vec.map(entry => entry.readValid | entry.writeValid).orR)

        val c_enq_ptr = Counter(params.writeBufEntries)
        val c_deq_ptr = Counter(params.writeBufEntries)
        val c_maybe_full = RegInit(false.B)
        val c_ptr_match = c_deq_ptr.value === c_enq_ptr.value
        val c_full = c_ptr_match && c_maybe_full
        val c_empty = c_ptr_match && !c_maybe_full

        val rs_mem = Mem(params.num_llc_mshrs * (params.num_write_beats + 1), chiselTypeOf(a_a.bits)) // each write occupies 4 slots. great.

        val rs_data_in = Wire(chiselTypeOf(out.a))
        
        TLArbiter(TLArbiter.roundRobin)(rs_data_in, (0.U, a_a), (edgeIn.numBeats1(c_a.bits), c_a))

        val c_addr_map = RegInit(VecInit(Seq.fill(params.writeBufEntries)(0.U.asTypeOf(Valid(chiselTypeOf(c_a.bits.address))))))
        val c_q_mem = Mem(params.writeBufEntries, chiselTypeOf(c_a.bits)) // an optimization exists here for multi-beat requests but I am simply too lazy to figure it out.

        // ready signals
        val repeat = WireInit(false.B)
        rs_data_in.ready := !repeat // when repeating, we are enqueing to the service queue, so it's not safe to put data into an RS
        
        val bandwidth_ctr = RegInit(0.U((log2Ceil(params.ram_bandiwdth)).W))

        // handle multi-beat nonsense and tagmatching
        val beats_left_in = RegInit(0.U((log2Ceil(params.num_write_beats)).W))
        val beats_left_out = RegInit(0.U((log2Ceil(params.num_write_beats)).W))
        val beats_init_out = (params.num_write_beats - 1).U

        // Service Queue implementation
        val rs_service_q_in = Wire(Decoupled(chiselTypeOf(rs_data_in.bits.source >> 1)))
        rs_service_q_in.valid := false.B
        rs_service_q_in.bits := DontCare
        val rs_out_sel = Queue(rs_service_q_in, params.num_llc_mshrs, pipe=false)
        rs_out_sel.ready := false.B
        val rs_out_rNw = Wire(Bool())
        val rs_out_base_addr = (rs_out_sel.bits << 2.U) + (rs_out_sel.bits)

        assert(!(!rs_empty && !rs_out_sel.valid))
        assert(!(rs_empty && rs_out_sel.valid))

        val rs_mem_data_out = rs_mem(Mux(rs_out_rNw, rs_out_base_addr, (rs_out_base_addr + Mux(beats_left_out === 0.U, 1.U, (params.num_write_beats.U - beats_left_out) + 1.U))))
        val tagmatch_wire = Cat(c_addr_map.map(entry => entry.bits === rs_mem_data_out.address && entry.valid).reverse) //write forwarding and coalescing

        val tagmatch_reg = RegEnable(tagmatch_wire, beats_left_out === 0.U)
        val tagmatch_ptrOH = Mux(beats_left_out === 0.U, tagmatch_wire, tagmatch_reg)
        val tagmatch_valid = tagmatch_ptrOH.orR

        val tagmatch_ptr_part = OHToUInt(tagmatch_ptrOH)
        val tagmatch_addr = RegInit(chiselTypeOf(a_a.bits.address), 0.U)
        val tagmatch_ptr = tagmatch_ptr_part + Mux(beats_left_out === 0.U, 0.U, (params.num_write_beats-1).U - beats_left_out)
        val tagmatch_latch = RegInit(false.B)

        // val addr_old = RegInit(chiselTypeOf(a_a.bits.address), 0.U)

        // bandwidth impl counter declaration
        val beats_init_tx = edgeOut.numBeats1(a_latency_bits)
        val beats_left_tx = RegInit(0.U(4.W))

        // general TODO changes:
        // [x] all enqueues go into RS 
        // [x] claim RS logic
        // [x] free RS logic
        // [x] dequeues from RS 
        // [x] pass write from RS to c_queue like we have below 
        // [x] service queue
        // enqueueing
        val rs_in_mshr_id = rs_data_in.bits.source >> 1.U
        val rs_in_base_addr = ((rs_data_in.bits.source >> 1.U) << 2.U) + (rs_data_in.bits.source >> 1.U) //surely this will get optimimzed reasonably, leaving as is for readability
        val rs_in_rNw = rs_data_in.bits.opcode === TLMessages.Get
        val rs_in_addr = Mux(rs_in_rNw, rs_in_base_addr, (rs_in_base_addr + Mux(beats_left_in === 0.U, 1.U, (params.num_write_beats.U - beats_left_in) + 1.U))) //implicit + 1

        val clear_read_rs = Wire(Bool())
        val clear_write_rs = Wire(Bool())
        clear_read_rs := false.B 
        clear_write_rs := false.B

        when (rs_data_in.fire) { // enq data into RS
          rs_mem(rs_in_addr) := rs_data_in.bits

          // update rs_valid_vec
          when (rs_in_rNw) {
            rs_valid_vec(rs_in_mshr_id).readValid := true.B
          }.otherwise {
            when (beats_left_in === 0.U) {
              rs_valid_vec(rs_in_mshr_id).writeValid := true.B
              beats_left_in := edgeIn.numBeats1(rs_data_in.bits)
            }.otherwise {
              beats_left_in := beats_left_in - 1.U
            }
          }
          when (beats_left_in === 0.U && !(rs_valid_vec(rs_in_mshr_id).readValid | rs_valid_vec(rs_in_mshr_id).writeValid)) {
            // add to service queue only if MSHR isn't already in queue
            rs_service_q_in.bits := rs_in_mshr_id
            rs_service_q_in.valid := true.B
          }
        }

        val valid_write = rs_valid_vec(rs_out_sel.bits).writeValid ||
            ((rs_data_in.bits.source >> 1 === rs_out_sel.bits) && 
            rs_data_in.valid && rs_data_in.bits.opcode =/= TLMessages.Get)
        val c_latch = RegInit(false.B)
        val c_wire = Wire(Bool())
        val do_write = Mux(c_wire, true.B, c_latch)
        c_wire := false.B

        val unsafe_write = c_deq && !do_write // don't need a counter, the ram BW itself will let things go through

        a_a.valid := in.a.valid && !toD && !unsafe_write
        c_a.valid := in.c.valid && in.c.bits.opcode === ReleaseData && !unsafe_write

        in.a.ready := Mux(toD, a_d.ready && !(tagmatch_valid || tagmatch_latch), (a_a.ready && !unsafe_write))
        in.c.ready := Mux(in.c.bits.opcode === Release, c_d.ready, (c_a.ready && !unsafe_write))

        rs_out_rNw := rs_valid_vec(rs_out_sel.bits).readValid && !(c_latch && !tagmatch_latch)

        // dequeues
        when (bandwidth_ctr === 0.U && !tagmatch_latch && !c_latch) {
          // RS always highest prio first
          when (rs_out_sel.valid) {
            // handle read vs write
            when (rs_out_rNw) { //read
              when(beats_left_tx === 0.U) {
                when (tagmatch_valid) { // forward
                  when (a_d.ready) {
                    clear_read_rs := true.B

                    printf(cf"bypassing request from source ${rs_out_sel.bits}\n")
                    tagmatch_latch := true.B
                    beats_left_out := (params.num_write_beats-1).U
                    tagmatch_addr := c_addr_map(tagmatch_ptr).bits

                    a_d.bits := edgeIn.Grant(
                      fromSink = 0.U,
                      toSource = rs_out_sel.bits,
                      lgSize = rs_mem_data_out.size,
                      capPermissions = TLPermissions.toT,
                      data = rs_mem_data_out.data
                    )
                    a_d.valid := true.B
                  }
                }.elsewhen(out.a.ready) {
                  clear_read_rs := true.B
                  a_latency_bits := rs_mem_data_out
                  a_latency_valid := true.B
                }
                
                when (clear_read_rs) {
                  // clear RS
                  rs_valid_vec(rs_out_sel.bits).readValid := false.B
                  rs_out_sel.ready := !valid_write || c_full
                  when (valid_write) { // manage following write
                    when (!c_full) {
                      c_latch := true.B 
                    }.otherwise {
                      repeat := rs_valid_vec(rs_out_sel.bits).writeValid
                      rs_service_q_in.bits := rs_out_sel.bits
                      rs_service_q_in.valid := true.B
                    }  
                  }
                }
              }
            }.otherwise { //writes
              c_latch := true.B
              c_wire := true.B
            }
          }.elsewhen (!c_empty) { // these writes are UNSAFE, need to guard them
            c_deq := true.B
            when (out.a.ready) {
              a_latency_bits := c_q_mem(c_deq_ptr.value)
              a_latency_valid := true.B 
              c_deq_ptr.inc()
              c_addr_map(c_deq_ptr.value).valid := false.B
              assert(c_q_mem(c_deq_ptr.value).opcode =/= TLMessages.Get)
            }
          }
        }

        when (tagmatch_latch) { //temportarily halt all dequeues to process forward
          when (a_d.ready) {
            printf(cf"bypassing request from source ${rs_out_sel.bits}\n")
            a_d.bits := edgeIn.Grant(
              fromSink = 0.U,
              toSource = rs_out_sel.bits,
              lgSize = rs_mem_data_out.size,
              capPermissions = TLPermissions.toT,
              data = c_q_mem(tagmatch_ptr).data
            )
            a_d.valid := true.B
            beats_left_out := beats_left_out - 1.U
            when (tagmatch_latch && beats_left_out === 1.U) { // last tagmatch beat
              rs_valid_vec(rs_out_sel.bits).readValid := false.B
              rs_out_sel.ready := true.B
              tagmatch_latch := false.B
            }
          }
        }.elsewhen (do_write) {
          when (c_full) { // push-through
            when (out.a.ready && c_a_d.ready) {
              clear_write_rs := true.B
              a_latency_bits := c_q_mem(c_deq_ptr.value)
              a_latency_valid := true.B
              c_deq_ptr.inc()
              c_deq := true.B 
              when (tagmatch_valid) {
                c_q_mem(tagmatch_ptr) := rs_mem_data_out
              }.otherwise {
                c_q_mem(c_enq_ptr.value) := rs_mem_data_out
                c_enq_ptr.inc()
                c_enq := true.B
                when (beats_left_out === 1.U) { // update address pointer in table on last beat, point to first beat
                  // THIS IS NOT SAFE FOR NON-POW2 SIZED WRITE BUFFERS.
                  c_addr_map(c_enq_ptr.value - beats_init_out).bits := rs_mem_data_out.address
                  c_addr_map(c_enq_ptr.value - beats_init_out).valid := true.B
                }
              }
            }
          }.otherwise {
            // enqueueing
            when (c_a_d.ready) {
              clear_write_rs := true.B
              // access data
              when (tagmatch_valid) { // do write coalesce
                c_q_mem(tagmatch_ptr) := rs_mem_data_out
              }.otherwise {
                printf(cf"enqueueing 0x${rs_mem_data_out.address}%x as opcode ${rs_mem_data_out.opcode}\n")
                c_enq := true.B
                c_q_mem(c_enq_ptr.value) := rs_mem_data_out
                c_enq_ptr.inc()
                when (beats_left_out === 1.U) { // update address pointer in table on last beat, point to first beat
                  // THIS IS NOT SAFE FOR NON-POW2 SIZED WRITE BUFFERS.
                  c_addr_map(c_enq_ptr.value - beats_init_out).bits := rs_mem_data_out.address
                  c_addr_map(c_enq_ptr.value - beats_init_out).valid := true.B
                }
              }
            }
          }
          when (clear_write_rs) {
            // ack writes
            when (beats_left_out === 0.U) { // only for first beat
              c_a_d.valid := true.B
              c_a_d.bits := edgeIn.ReleaseAck(
                toSource = rs_mem_data_out.source >> 1,
                lgSize = rs_mem_data_out.size,
                denied = false.B)
              // set beats left_out for write
              beats_left_out := (params.num_write_beats-1).U
            }.otherwise {
              beats_left_out := beats_left_out - 1.U
            }
            // clear RS on last beat
            when (beats_left_out === 1.U) {
              rs_valid_vec(rs_out_sel.bits).writeValid := false.B
              rs_out_sel.ready := true.B
              c_latch := false.B
              // append read to service queue if it arrived late, extra guard for passthrough
              when (rs_valid_vec(rs_out_sel.bits).readValid || 
                ((rs_data_in.bits.source >> 1 === rs_out_sel.bits) && 
                rs_data_in.valid && rs_data_in.bits.opcode === TLMessages.Get)) {
                  repeat := rs_valid_vec(rs_out_sel.bits).readValid
                  rs_service_q_in.bits := rs_out_sel.bits
                  rs_service_q_in.valid := true.B
              }
            }
            assert(c_q_mem(c_deq_ptr.value).opcode =/= TLMessages.Get)
            assert(rs_mem_data_out.opcode =/= TLMessages.Get)
            assert(rs_mem_data_out.size === 6.U) // temp debug assert
          }
        }

        // update full/empty
        when (c_deq =/= c_enq) {
          c_maybe_full := c_enq
        }

        val dec_counter = Wire(Bool())
        val reset_counter = Wire(Bool())
        dec_counter := false.B
        reset_counter := false.B

        bandwidth_ctr := Mux(reset_counter, params.ram_bandiwdth.U, 
            Mux(dec_counter, bandwidth_ctr - 1.U, bandwidth_ctr))

        when (out.a.ready && !tagmatch_latch) {
          when (a_latency_valid) {
            when (bandwidth_ctr === 0.U && (beats_init_tx === 0.U || beats_left_tx === 1.U)) {
              reset_counter := true.B
            }
            beats_left_tx := Mux(beats_init_tx =/= 1.U, Mux(beats_left_tx === 0.U, beats_init_tx, beats_left_tx - 1.U), 0.U)
            when (a_latency_bits.opcode === 4.U) {assert(beats_init_tx === 0.U, cf"actual = ${beats_init_tx}, size = ${a_latency_bits.size}")}
            when (a_latency_bits.opcode === 0.U) {assert(beats_init_tx === 3.U, cf"actual = ${beats_init_tx}, size = ${a_latency_bits.size}")}
          }
          when (bandwidth_ctr =/= 0.U) {
            dec_counter := true.B
          }
        }

        when ((beats_left_tx =/= 0.U) && out.a.ready) { assert(a_latency_valid, "A went invalid in the middle of a txn")}

        // Tie off unused ports
        in.b.valid := false.B
        out.c.valid := false.B
        out.e.valid := false.B
      }
    }
  }
}

object TLRRCacheCork
{
  def apply(params: TLCacheCorkParams)(implicit p: Parameters): TLNode =
  {
    val cork = LazyModule(new TLRRCacheCork(params))
    cork.node
  }
  def apply(unsafe: Boolean = false, sinkIds: Int = 8)(implicit p: Parameters): TLNode =
  {
    apply(TLCacheCorkParams(unsafe, sinkIds))
  }
}

class TLSplitPrioCacheCork(params: TLCacheCorkParams = TLCacheCorkParams())(implicit p: Parameters) extends LazyModule
{
  val unsafe = params.unsafe
  val sinkIds = params.sinkIds
  val node = TLAdapterNode(
    clientFn  = { case cp =>
      cp.v1copy(clients = cp.clients.map { c => c.v1copy(
        supportsProbe = TransferSizes.none,
        sourceId = IdRange(c.sourceId.start*2, c.sourceId.end*2))})},
    managerFn = { case mp =>
      mp.v1copy(
        endSinkId = if (mp.managers.exists(_.regionType == RegionType.UNCACHED)) sinkIds else 0,
        managers = mp.managers.map { m => m.v1copy(
          supportsAcquireB = if (m.regionType == RegionType.UNCACHED) m.supportsGet     else m.supportsAcquireB,
          supportsAcquireT = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull.intersect(m.supportsGet) else m.supportsAcquireT,
          alwaysGrantsT    = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull else m.alwaysGrantsT)})})

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    (node.in zip node.out) foreach { case ((in, edgeIn), (out, edgeOut)) =>
      // If this adapter does not need to do anything, toss all the above work and just directly connect
      if (!edgeIn.manager.anySupportAcquireB) {
        out <> in
      } else {
        val clients = edgeIn.client.clients
        val caches = clients.filter(_.supports.probe)
        require (clients.size == 1 || caches.size == 0 || unsafe, s"Only one client can safely use a TLCacheCork; ${clients.map(_.name)}")
        require (caches.size <= 1 || unsafe, s"Only one caching client allowed; ${clients.map(_.name)}")
        edgeOut.manager.managers.foreach { case m =>
          require (!m.supportsAcquireB || unsafe, s"Cannot support caches beyond the Cork; ${m.name}")
          require (m.regionType <= RegionType.UNCACHED)
        }

        // The Cork turns [Acquire=>Get] => [AccessAckData=>GrantData]
        //            and [ReleaseData=>PutFullData] => [AccessAck=>ReleaseAck]
        // We need to encode information sufficient to reverse the transformation in output.
        // A caveat is that we get Acquire+Release with the same source and must keep the
        // source unique after transformation onto the A channel.
        // The coding scheme is:
        //   Release, AcquireBlock.BtoT, AcquirePerm => instant response
        //   Put{Full,Partial}Data: 1, ReleaseData: 0 => AccessAck
        //   {Arithmetic,Logical}Data,Get: 0, Acquire: 1 => AccessAckData
        //   Hint:0 => HintAck

        // The CacheCork can potentially send the same source twice if a client sends
        // simultaneous Release and AMO/Get with the same source. It will still correctly
        // decode the messages based on the D.opcode, but the double use violates the spec.
        // Fortunately, no masters we know of behave this way!

        // Take requests from A to A or D (if BtoT Acquire)
        val a_a = Wire(chiselTypeOf(out.a))
        val a_d = Wire(chiselTypeOf(in.d))
        val isPut = in.a.bits.opcode === PutFullData || in.a.bits.opcode === PutPartialData
        val toD = (in.a.bits.opcode === AcquireBlock && in.a.bits.param === TLPermissions.BtoT) ||
                  (in.a.bits.opcode === AcquirePerm)

        // latency implementation
        val a_latency_bits = Wire(chiselTypeOf(out.a.bits))
        val a_latency_valid = Wire(chiselTypeOf(out.a.valid))
        out.a.bits := ShiftRegister(a_latency_bits, params.ram_latency - 4, out.a.ready)
        out.a.valid := ShiftRegister(a_latency_valid, params.ram_latency - 4, out.a.ready)

        a_a.bits := in.a.bits
        a_a.bits.source := in.a.bits.source << 1 | Mux(isPut, 1.U, 0.U)

        // Transform Acquire into Get
        when (in.a.bits.opcode === AcquireBlock || in.a.bits.opcode === AcquirePerm) {
          a_a.bits.opcode := Get
          a_a.bits.param  := 0.U
          a_a.bits.source := in.a.bits.source << 1 | 1.U
        }

        // Upgrades are instantly successful
        a_d.valid := in.a.valid && toD
        a_d.bits := edgeIn.Grant(
          fromSink = 0.U,
          toSource = in.a.bits.source,
          lgSize   = in.a.bits.size,
          capPermissions = TLPermissions.toT)

        // Take ReleaseData from C to A; Release from C to D
        val c_a = Wire(chiselTypeOf(out.a))
        c_a.valid := in.c.valid && in.c.bits.opcode === ReleaseData
        c_a.bits := edgeOut.Put(
          fromSource = in.c.bits.source << 1,
          toAddress  = in.c.bits.address,
          lgSize     = in.c.bits.size,
          data       = in.c.bits.data,
          corrupt    = in.c.bits.corrupt)._2
        c_a.bits.user :<= in.c.bits.user

        // Releases without Data succeed instantly
        val c_d = Wire(chiselTypeOf(in.d))
        c_d.valid := in.c.valid && in.c.bits.opcode === Release
        c_d.bits := edgeIn.ReleaseAck(in.c.bits)
        // Releases that enter the write queue respond early
        val c_a_d = Wire(chiselTypeOf(in.d))
        c_a_d.bits := edgeIn.ReleaseAck(in.c.bits)
        c_a_d.valid := false.B

        assert (!in.c.valid || in.c.bits.opcode === Release || in.c.bits.opcode === ReleaseData)
        in.c.ready := Mux(in.c.bits.opcode === Release, c_d.ready, c_a.ready)

        // Discard E
        in.e.ready := true.B

        // Block B; should never happen
        out.b.ready := false.B
        assert (!out.b.valid)

        // Track in-flight sinkIds
        val pool = Module(new IDPool(sinkIds))
        pool.io.free.valid := in.e.fire
        pool.io.free.bits  := in.e.bits.sink

        val in_d = Wire(chiselTypeOf(in.d))
        val d_first = edgeOut.first(in_d)
        val d_grant = in_d.bits.opcode === GrantData || in_d.bits.opcode === Grant
        pool.io.alloc.ready := in.d.fire && d_first && d_grant
        in.d.valid := in_d.valid && (pool.io.alloc.valid || !d_first || !d_grant)
        in_d.ready := in.d.ready && (pool.io.alloc.valid || !d_first || !d_grant)
        in.d.bits := in_d.bits
        in.d.bits.sink := pool.io.alloc.bits holdUnless d_first

        // Take responses from D and transform them
        val d_d = Wire(chiselTypeOf(in.d))
        d_d <> out.d
        d_d.bits.source := out.d.bits.source >> 1

        // Record if a target was writable and auto-promote toT if it was
        // This is structured so that the vector can be constant prop'd away
        val wSourceVec = Reg(Vec(edgeIn.client.endSourceId, Bool()))
        val aWOk = edgeIn.manager.fastProperty(in.a.bits.address, !_.supportsPutFull.none, (b:Boolean) => b.B)
        val dWOk = wSourceVec(d_d.bits.source)
        val bypass = (edgeIn.manager.minLatency == 0).B && in.a.valid && in.a.bits.source === d_d.bits.source
        val dWHeld = Mux(bypass, aWOk, dWOk) holdUnless d_first

        when (in.a.fire) {
          wSourceVec(in.a.bits.source) := aWOk
        }

        // Wipe out any unused registers
        edgeIn.client.unusedSources.foreach { id =>
          wSourceVec(id) := edgeIn.manager.anySupportPutFull.B
        }

        when (out.d.bits.opcode === AccessAckData && out.d.bits.source(0)) {
          d_d.bits.opcode := GrantData
          d_d.bits.param := Mux(dWHeld, TLPermissions.toT, TLPermissions.toB)
        }
        when (out.d.bits.opcode === AccessAck && !out.d.bits.source(0)) {
          //d_d.bits.opcode := ReleaseAck
          // we respond to release when it enters write queue, not here
          d_d.valid := false.B
        }

        // Combine the sources of messages into the channels
        // TLArbiter(TLArbiter.lowestIndexFirst)(out.a, (edgeOut.numBeats1(c_a.bits), c_a), (edgeOut.numBeats1(a_a.bits), a_a))
        a_latency_valid := false.B 
        a_latency_bits := DontCare
        TLArbiter(TLArbiter.lowestIndexFirst)(in_d, (edgeIn.numBeats1(d_d.bits), d_d), (0.U, Queue(c_a_d, 2)), (0.U, Queue(c_d, 2)), (edgeIn.numBeats1(a_d.bits), Queue(a_d, 8)))

        // implement two queues: write queue and high-priority queue.
        val c_enq = Wire(Bool())
        val c_deq = Wire(Bool())
        val a_enq = Wire(Bool())
        val a_deq = Wire(Bool())
        c_enq := false.B
        c_deq := false.B
        a_enq := false.B
        a_deq := false.B

        // high-priority queue is a bigger queue with no fancy things going on.
        val a_enq_ptr = Counter(params.a_queue_depth)
        val a_deq_ptr = Counter(params.a_queue_depth)
        val a_maybe_full = RegInit(false.B)
        val a_ptr_match = a_deq_ptr.value === a_enq_ptr.value
        val a_full = a_ptr_match && a_maybe_full
        val a_empty = a_ptr_match && !a_maybe_full

        val c_enq_ptr = Counter(params.writeBufEntries)
        val c_deq_ptr = Counter(params.writeBufEntries)
        val c_maybe_full = RegInit(false.B)
        val c_ptr_match = c_deq_ptr.value === c_enq_ptr.value
        val c_full = c_ptr_match && c_maybe_full
        val c_empty = c_ptr_match && !c_maybe_full

        val a_q_mem = Mem(params.a_queue_depth, chiselTypeOf(a_a.bits)) // each write occupies 4 slots. great.

        // this wire carries bypass
        val c_a_to_a_queue = Wire(chiselTypeOf(out.a))
        val enq_c_req_to_a = RegInit(false.B)
        c_a_to_a_queue.bits := c_a.bits
        c_a_to_a_queue.valid := c_a.valid && (enq_c_req_to_a || c_full)

        val out_a_q = Wire(chiselTypeOf(out.a))
        
        TLArbiter(TLArbiter.roundRobin)(out_a_q, (edgeIn.numBeats1(c_a_to_a_queue.bits), c_a_to_a_queue), (0.U, a_a))

        when (c_full) { // switch to enqueing to a when writebuff fills
          enq_c_req_to_a := true.B
        }.elsewhen (a_empty) { // switch back only when high prio queue empties and c is no longer full.
          enq_c_req_to_a := false.B 
        }

        val c_addr_map = RegInit(VecInit(Seq.fill(params.writeBufEntries)(0.U.asTypeOf(Valid(chiselTypeOf(c_a.bits.address))))))
        val c_q_mem = Mem(params.writeBufEntries, chiselTypeOf(c_a.bits)) // an optimization exists here for multi-beat requests but I am simply too lazy to figure it out.

        // ready signals
        c_a.ready := (!(c_full || a_deq || enq_c_req_to_a)) || c_a_to_a_queue.fire
        out_a_q.ready := !a_full
        a_a.valid := in.a.valid && !toD && !c_deq

        // handle multi-beat nonsense and tagmatching
        val bandwidth_ctr = RegInit(0.U(8.W))
        val beats_left_tgmtch = RegInit(0.U(4.W)) // if you have more than 16 beats, go kick rocks ig

        val tagmatch_me = Mux(a_deq, a_q_mem(a_deq_ptr.value).address, c_a.bits.address)
        val tagmatch_wire = Cat(c_addr_map.map(entry => entry.bits === tagmatch_me && entry.valid).reverse) //write forwarding and coalescing

        val tagmatch_reg = RegEnable(tagmatch_wire, beats_left_tgmtch === 0.U)
        val tagmatch_ptrOH = Mux(beats_left_tgmtch === 0.U, tagmatch_wire, tagmatch_reg)
        val tagmatch_valid = tagmatch_ptrOH.orR

        val tagmatch_ptr_part = OHToUInt(tagmatch_ptrOH)
        val beats_init_tgmtch = edgeIn.numBeats1(c_q_mem(tagmatch_ptr_part))
        val tagmatch_addr = RegInit(chiselTypeOf(a_a.bits.address), 0.U)
        val tagmatch_ptr = tagmatch_ptr_part + Mux(beats_left_tgmtch === 0.U, 0.U, beats_init_tgmtch - beats_left_tgmtch + 1.U)
        val tagmatch_latch = RegInit(false.B)

        in.a.ready := Mux(toD, a_d.ready && !(tagmatch_valid || tagmatch_latch), (a_a.ready && !c_deq))

        val addr_old = RegInit(chiselTypeOf(a_a.bits.address), 0.U)

        val beats_init_c = edgeIn.numBeats1(c_a.bits)
        val beats_left_c = RegInit(0.U(4.W))

        // bandwidth impl
        val beats_init_tx = edgeOut.numBeats1(a_latency_bits)
        val beats_left_tx = RegInit(0.U(4.W))

        when (c_enq) {
          beats_left_c := Mux(beats_left_c === 0.U, beats_init_c, beats_left_c - 1.U)
        }

        // enqueueing
        when (c_a.fire && !c_a_to_a_queue.valid) { //enq write to C queue
          // send resp immediately
          when(beats_left_c === 0.U) {
            c_a_d.valid := true.B
          }
          // access data
          when (tagmatch_valid) { // do write coalesce
            c_q_mem(tagmatch_ptr) := c_a.bits
          }.otherwise {
            printf(cf"enqueueing 0x${c_a.bits.address}%x as opcode ${c_a.bits.opcode}\n")
            c_enq := true.B
            c_q_mem(c_enq_ptr.value) := c_a.bits
            c_enq_ptr.inc()
            when (beats_left_c === 1.U) { // update address pointer in table on last beat, point to first beat
              c_addr_map(c_enq_ptr.value - beats_init_c).bits := c_a.bits.address
              c_addr_map(c_enq_ptr.value - beats_init_c).valid := true.B
            }
          }
        }
        when (out_a_q.fire) { // enq read
          a_enq := true.B
          a_q_mem(a_enq_ptr.value) := out_a_q.bits
          a_enq_ptr.inc()
        }

        // dequeues
        when (bandwidth_ctr === 0.U && !tagmatch_latch) {
          // always highest prio first
          when (!a_empty) {
            // handle read vs write
            when (a_q_mem(a_deq_ptr.value).opcode === TLMessages.Get) { //read
              when(beats_left_tx === 0.U) {
                a_deq := true.B
                when (tagmatch_valid) { // forward
                  when (a_d.ready) {
                    printf(cf"bypassing request from source ${a_q_mem(a_deq_ptr.value).source >> 1}\n")
                    tagmatch_latch := true.B
                    beats_left_tgmtch := beats_init_tgmtch
                    tagmatch_addr := c_addr_map(tagmatch_ptr).bits

                    a_d.bits := edgeIn.Grant(
                      fromSink = 0.U,
                      toSource = a_q_mem(a_deq_ptr.value).source >> 1,
                      lgSize = a_q_mem(a_deq_ptr.value).size,
                      capPermissions = TLPermissions.toT,
                      data = c_q_mem(tagmatch_ptr).data
                    )
                    a_d.valid := true.B
                  }
                }.elsewhen(out.a.ready) {
                  a_latency_bits := a_q_mem(a_deq_ptr.value)
                  a_latency_valid := true.B
                  a_deq_ptr.inc()
                }
              }
            }.otherwise { //writes
              when (out.a.ready && c_a_d.ready) {
                a_latency_bits := c_q_mem(c_deq_ptr.value)
                a_latency_valid := true.B
                a_deq_ptr.inc()
                a_deq := true.B
                c_deq_ptr.inc()
                c_deq := true.B 
                when (tagmatch_valid) {
                  c_q_mem(tagmatch_ptr) := a_q_mem(a_deq_ptr.value)
                }.otherwise {
                  c_q_mem(c_enq_ptr.value) := a_q_mem(a_deq_ptr.value)
                  c_enq_ptr.inc()
                  c_enq := true.B
                  when (beats_left_tx === 1.U) { // update address pointer in table on last beat, point to first beat
                      // THIS IS NOT SAFE FOR NON-POW2 SIZED WRITE BUFFERS.
                      c_addr_map(c_enq_ptr.value - beats_init_tx).bits := a_q_mem(a_deq_ptr.value).address
                      c_addr_map(c_enq_ptr.value - beats_init_tx).valid := true.B
                  }
                }
                // ack write
                when(addr_old =/= a_q_mem(a_deq_ptr.value).address) { // only for first beat
                  c_a_d.valid := true.B
                  c_a_d.bits := edgeIn.ReleaseAck(
                    toSource = a_q_mem(a_deq_ptr.value).source >> 1,
                    lgSize = a_q_mem(a_deq_ptr.value).size,
                    denied = false.B)
                  addr_old := a_q_mem(a_deq_ptr.value).address
                }
              }
            }
          }.elsewhen (!c_empty) {
            c_deq := true.B
            when (out.a.ready) {
              a_latency_bits := c_q_mem(c_deq_ptr.value)
              a_latency_valid := true.B 
              c_deq_ptr.inc()
              c_addr_map(c_deq_ptr.value).valid := false.B
            }
          }
        }.elsewhen (!a_empty && !c_full && a_q_mem(a_deq_ptr.value).opcode =/= TLMessages.Get && beats_left_c =/= 0.U && !tagmatch_latch) {
          // catch corner where c empties out while a is getting a put request
          // this is naive and only doing residual requests, we already caught tagmatches
          c_enq := true.B
          a_deq := true.B
          a_deq_ptr.inc()
          c_enq_ptr.inc()
          c_q_mem(c_enq_ptr.value) := a_q_mem(a_deq_ptr.value)
        }

        when (tagmatch_latch) { //temportarily halt all dequeues to process forward
          a_deq := true.B
          when (a_d.ready) {
            printf(cf"bypassing request from source ${a_q_mem(a_deq_ptr.value).source >> 1}\n")
            a_d.bits := edgeIn.Grant(
              fromSink = 0.U,
              toSource = a_q_mem(a_deq_ptr.value).source >> 1,
              lgSize = a_q_mem(a_deq_ptr.value).size,
              capPermissions = TLPermissions.toT,
              data = c_q_mem(tagmatch_ptr).data
            )
            a_d.valid := true.B
            beats_left_tgmtch := beats_left_tgmtch - 1.U
            when (tagmatch_latch && beats_left_tgmtch === 1.U) { // last tagmatch beat
              a_deq_ptr.inc()
              tagmatch_latch := false.B
            }
          }
        }

        // update full/empty
        when (c_deq =/= c_enq) {
          c_maybe_full := c_enq
        }
        when (a_deq =/= a_enq) {
          a_maybe_full := a_enq
        }

        val dec_counter = Wire(Bool())
        val reset_counter = Wire(Bool())
        dec_counter := false.B
        reset_counter := false.B

        bandwidth_ctr := Mux(reset_counter, params.ram_bandiwdth.U, 
            Mux(dec_counter, bandwidth_ctr - 1.U, bandwidth_ctr))

        when (out.a.ready && !tagmatch_latch) {
          when (a_latency_valid) {
            when (bandwidth_ctr === 0.U && (beats_init_tx === 0.U || beats_left_tx === 1.U)) {
              reset_counter := true.B
            }
            beats_left_tx := Mux(beats_init_tx =/= 1.U, Mux(beats_left_tx === 0.U, beats_init_tx, beats_left_tx - 1.U), 0.U)
            when (a_latency_bits.opcode === 4.U) {assert(beats_init_tx === 0.U)}
            when (a_latency_bits.opcode === 0.U) {assert(beats_init_tx === 3.U)}
          }
          when (bandwidth_ctr =/= 0.U) {
            dec_counter := true.B
          }
        }

        // Tie off unused ports
        in.b.valid := false.B
        out.c.valid := false.B
        out.e.valid := false.B
      }
    }
  }
}

object TLSplitPrioCacheCork
{
  def apply(params: TLCacheCorkParams)(implicit p: Parameters): TLNode =
  {
    val cork = LazyModule(new TLSplitPrioCacheCork(params))
    cork.node
  }
  def apply(unsafe: Boolean = false, sinkIds: Int = 8)(implicit p: Parameters): TLNode =
  {
    apply(TLCacheCorkParams(unsafe, sinkIds))
  }
}


class TLCacheCork(params: TLCacheCorkParams = TLCacheCorkParams())(implicit p: Parameters) extends LazyModule
{
  val unsafe = params.unsafe
  val sinkIds = params.sinkIds
  val node = TLAdapterNode(
    clientFn  = { case cp =>
      cp.v1copy(clients = cp.clients.map { c => c.v1copy(
        supportsProbe = TransferSizes.none,
        sourceId = IdRange(c.sourceId.start*2, c.sourceId.end*2))})},
    managerFn = { case mp =>
      mp.v1copy(
        endSinkId = if (mp.managers.exists(_.regionType == RegionType.UNCACHED)) sinkIds else 0,
        managers = mp.managers.map { m => m.v1copy(
          supportsAcquireB = if (m.regionType == RegionType.UNCACHED) m.supportsGet     else m.supportsAcquireB,
          supportsAcquireT = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull.intersect(m.supportsGet) else m.supportsAcquireT,
          alwaysGrantsT    = if (m.regionType == RegionType.UNCACHED) m.supportsPutFull else m.alwaysGrantsT)})})

  lazy val module = new Impl
  class Impl extends LazyModuleImp(this) {
    (node.in zip node.out) foreach { case ((in, edgeIn), (out, edgeOut)) =>
      // If this adapter does not need to do anything, toss all the above work and just directly connect
      if (!edgeIn.manager.anySupportAcquireB) {
        out <> in
      } else {
        val clients = edgeIn.client.clients
        val caches = clients.filter(_.supports.probe)
        require (clients.size == 1 || caches.size == 0 || unsafe, s"Only one client can safely use a TLCacheCork; ${clients.map(_.name)}")
        require (caches.size <= 1 || unsafe, s"Only one caching client allowed; ${clients.map(_.name)}")
        edgeOut.manager.managers.foreach { case m =>
          require (!m.supportsAcquireB || unsafe, s"Cannot support caches beyond the Cork; ${m.name}")
          require (m.regionType <= RegionType.UNCACHED)
        }

        // The Cork turns [Acquire=>Get] => [AccessAckData=>GrantData]
        //            and [ReleaseData=>PutFullData] => [AccessAck=>ReleaseAck]
        // We need to encode information sufficient to reverse the transformation in output.
        // A caveat is that we get Acquire+Release with the same source and must keep the
        // source unique after transformation onto the A channel.
        // The coding scheme is:
        //   Release, AcquireBlock.BtoT, AcquirePerm => instant response
        //   Put{Full,Partial}Data: 1, ReleaseData: 0 => AccessAck
        //   {Arithmetic,Logical}Data,Get: 0, Acquire: 1 => AccessAckData
        //   Hint:0 => HintAck

        // The CacheCork can potentially send the same source twice if a client sends
        // simultaneous Release and AMO/Get with the same source. It will still correctly
        // decode the messages based on the D.opcode, but the double use violates the spec.
        // Fortunately, no masters we know of behave this way!

        // Take requests from A to A or D (if BtoT Acquire)
        val a_a = Wire(chiselTypeOf(out.a))
        val a_d = Wire(chiselTypeOf(in.d))
        val isPut = in.a.bits.opcode === PutFullData || in.a.bits.opcode === PutPartialData
        val toD = (in.a.bits.opcode === AcquireBlock && in.a.bits.param === TLPermissions.BtoT) ||
                  (in.a.bits.opcode === AcquirePerm)
        in.a.ready := Mux(toD, a_d.ready, a_a.ready)

        a_a.valid := in.a.valid && !toD
        a_a.bits := in.a.bits
        a_a.bits.source := in.a.bits.source << 1 | Mux(isPut, 1.U, 0.U)

        // Transform Acquire into Get
        when (in.a.bits.opcode === AcquireBlock || in.a.bits.opcode === AcquirePerm) {
          a_a.bits.opcode := Get
          a_a.bits.param  := 0.U
          a_a.bits.source := in.a.bits.source << 1 | 1.U
        }

        // Upgrades are instantly successful
        a_d.valid := in.a.valid && toD
        a_d.bits := edgeIn.Grant(
          fromSink = 0.U,
          toSource = in.a.bits.source,
          lgSize   = in.a.bits.size,
          capPermissions = TLPermissions.toT)

        // Take ReleaseData from C to A; Release from C to D
        val c_a = Wire(chiselTypeOf(out.a))
        c_a.valid := in.c.valid && in.c.bits.opcode === ReleaseData
        c_a.bits := edgeOut.Put(
          fromSource = in.c.bits.source << 1,
          toAddress  = in.c.bits.address,
          lgSize     = in.c.bits.size,
          data       = in.c.bits.data,
          corrupt    = in.c.bits.corrupt)._2
        c_a.bits.user :<= in.c.bits.user

        // Releases without Data succeed instantly
        val c_d = Wire(chiselTypeOf(in.d))
        c_d.valid := in.c.valid && in.c.bits.opcode === Release
        c_d.bits := edgeIn.ReleaseAck(in.c.bits)

        assert (!in.c.valid || in.c.bits.opcode === Release || in.c.bits.opcode === ReleaseData)
        in.c.ready := Mux(in.c.bits.opcode === Release, c_d.ready, c_a.ready)

        // Discard E
        in.e.ready := true.B

        // Block B; should never happen
        out.b.ready := false.B
        assert (!out.b.valid)

        // Track in-flight sinkIds
        val pool = Module(new IDPool(sinkIds))
        pool.io.free.valid := in.e.fire
        pool.io.free.bits  := in.e.bits.sink

        val in_d = Wire(chiselTypeOf(in.d))
        val d_first = edgeOut.first(in_d)
        val d_grant = in_d.bits.opcode === GrantData || in_d.bits.opcode === Grant
        pool.io.alloc.ready := in.d.fire && d_first && d_grant
        in.d.valid := in_d.valid && (pool.io.alloc.valid || !d_first || !d_grant)
        in_d.ready := in.d.ready && (pool.io.alloc.valid || !d_first || !d_grant)
        in.d.bits := in_d.bits
        in.d.bits.sink := pool.io.alloc.bits holdUnless d_first

        // Take responses from D and transform them
        val d_d = Wire(chiselTypeOf(in.d))
        d_d <> out.d
        d_d.bits.source := out.d.bits.source >> 1

        // Record if a target was writable and auto-promote toT if it was
        // This is structured so that the vector can be constant prop'd away
        val wSourceVec = Reg(Vec(edgeIn.client.endSourceId, Bool()))
        val aWOk = edgeIn.manager.fastProperty(in.a.bits.address, !_.supportsPutFull.none, (b:Boolean) => b.B)
        val dWOk = wSourceVec(d_d.bits.source)
        val bypass = (edgeIn.manager.minLatency == 0).B && in.a.valid && in.a.bits.source === d_d.bits.source
        val dWHeld = Mux(bypass, aWOk, dWOk) holdUnless d_first

        when (in.a.fire) {
          wSourceVec(in.a.bits.source) := aWOk
        }

        // Wipe out any unused registers
        edgeIn.client.unusedSources.foreach { id =>
          wSourceVec(id) := edgeIn.manager.anySupportPutFull.B
        }

        when (out.d.bits.opcode === AccessAckData && out.d.bits.source(0)) {
          d_d.bits.opcode := GrantData
          d_d.bits.param := Mux(dWHeld, TLPermissions.toT, TLPermissions.toB)
        }
        when (out.d.bits.opcode === AccessAck && !out.d.bits.source(0)) {
          d_d.bits.opcode := ReleaseAck
        }

        // Combine the sources of messages into the channels
        TLArbiter(TLArbiter.lowestIndexFirst)(out.a, (edgeOut.numBeats1(c_a.bits), c_a), (edgeOut.numBeats1(a_a.bits), a_a))
        TLArbiter(TLArbiter.lowestIndexFirst)(in_d,  (edgeIn .numBeats1(d_d.bits), d_d), (0.U, Queue(c_d, 2)), (0.U, Queue(a_d, 2)))

        // Tie off unused ports
        in.b.valid := false.B
        out.c.valid := false.B
        out.e.valid := false.B
      }
    }
  }
}

object TLCacheCork
{
  def apply(params: TLCacheCorkParams)(implicit p: Parameters): TLNode =
  {
    val cork = LazyModule(new TLCacheCork(params))
    cork.node
  }
  def apply(unsafe: Boolean = false, sinkIds: Int = 8)(implicit p: Parameters): TLNode =
  {
    apply(TLCacheCorkParams(unsafe, sinkIds))
  }
}
