;;! target = "x86_64"
;;! test = "clif"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation=false -W memory64 -O static-memory-maximum-size=0 -O static-memory-guard-size=0 -O dynamic-memory-guard-size=0"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i64 1)

  (func (export "do_store") (param i64 i32)
    local.get 0
    local.get 1
    i32.store offset=0x1000)

  (func (export "do_load") (param i64) (result i32)
    local.get 0
    i32.load offset=0x1000))

;; function u0:0(i64 vmctx, i64, i64, i32) tail {
;;     gv0 = vmctx
;;     gv1 = load.i64 notrap aligned gv0+104
;;     gv2 = load.i64 notrap aligned checked gv0+96
;;
;;                                 block0(v0: i64, v1: i64, v2: i64, v3: i32):
;; @0040                               v4 = global_value.i64 gv1
;; @0040                               v5 = iconst.i64 4100
;; @0040                               v6 = isub v4, v5  ; v5 = 4100
;; @0040                               v7 = icmp ugt v2, v6
;; @0040                               trapnz v7, heap_oob
;; @0040                               v8 = global_value.i64 gv2
;; @0040                               v9 = iadd v8, v2
;; @0040                               v10 = iconst.i64 4096
;; @0040                               v11 = iadd v9, v10  ; v10 = 4096
;; @0040                               store little heap v3, v11
;; @0044                               jump block1
;;
;;                                 block1:
;; @0044                               return
;; }
;;
;; function u0:1(i64 vmctx, i64, i64) -> i32 tail {
;;     gv0 = vmctx
;;     gv1 = load.i64 notrap aligned gv0+104
;;     gv2 = load.i64 notrap aligned checked gv0+96
;;
;;                                 block0(v0: i64, v1: i64, v2: i64):
;; @0049                               v4 = global_value.i64 gv1
;; @0049                               v5 = iconst.i64 4100
;; @0049                               v6 = isub v4, v5  ; v5 = 4100
;; @0049                               v7 = icmp ugt v2, v6
;; @0049                               trapnz v7, heap_oob
;; @0049                               v8 = global_value.i64 gv2
;; @0049                               v9 = iadd v8, v2
;; @0049                               v10 = iconst.i64 4096
;; @0049                               v11 = iadd v9, v10  ; v10 = 4096
;; @0049                               v12 = load.i32 little heap v11
;; @004d                               jump block1(v12)
;;
;;                                 block1(v3: i32):
;; @004d                               return v3
;; }
