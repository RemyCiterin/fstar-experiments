open Prims
type gst_pre = unit
type ('a, 'pre) gst_post' = unit
type 'a gst_post = unit
type 'a gst_wp = unit
type ('a, 'wp, 'p, 'h) lift_div_gst = 'wp
type ('h1, 'h2) heap_rel = unit
let (gst_get : unit -> FStar_Monotonic_Heap.heap) =
  fun uu___ -> failwith "Not yet implemented:gst_get"
let (gst_put : FStar_Monotonic_Heap.heap -> unit) =
  fun h1 -> failwith "Not yet implemented:gst_put"
type heap_predicate = unit
type 'p stable = unit
type 'p witnessed =
  (FStar_Monotonic_Heap.heap, unit, 'p) FStar_Monotonic_Witnessed.witnessed
let gst_witness : 'p . unit -> unit =
  fun uu___ -> failwith "Not yet implemented:gst_witness"
let gst_recall : 'p . unit -> unit =
  fun uu___ -> failwith "Not yet implemented:gst_recall"

type st_pre = unit
type ('a, 'pre) st_post' = unit
type 'a st_post = unit
type 'a st_wp = unit
type ('a, 'wp, 'uuuuu, 'uuuuu1) lift_gst_state = 'wp
type ('a, 'rel, 'r, 'h) contains_pred =
  ('a, 'rel, unit, unit) FStar_Monotonic_Heap.contains
type ('a, 'rel) mref = ('a, 'rel) FStar_Monotonic_Heap.mref
let recall : 'a 'rel . ('a, 'rel) mref -> unit = fun r -> ()
let alloc : 'a 'rel . 'a -> ('a, 'rel) mref =
  fun init ->
    let h0 = gst_get () in
    let uu___ = FStar_Monotonic_Heap.alloc h0 init false in
    match uu___ with | (r, h1) -> (gst_put h1; r)
let read : 'a 'rel . ('a, 'rel) mref -> 'a =
  fun r -> let h0 = gst_get () in FStar_Monotonic_Heap.sel_tot h0 r
let write : 'a 'rel . ('a, 'rel) mref -> 'a -> unit =
  fun r ->
    fun v ->
      let h0 = gst_get () in
      let h1 = FStar_Monotonic_Heap.upd_tot h0 r v in gst_put h1
let (get : unit -> FStar_Monotonic_Heap.heap) = fun u -> gst_get ()
let op_Bang : 'a 'rel . ('a, 'rel) mref -> 'a = fun r -> read r
let op_Colon_Equals : 'a 'rel . ('a, 'rel) mref -> 'a -> unit =
  fun r -> fun v -> write r v
type 'a ref = ('a, unit) mref
type ('h0, 'h1) modifies_none = unit