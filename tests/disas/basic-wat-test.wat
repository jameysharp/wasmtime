;;! target = "x86_64"

(module
  (memory 0)
  (func (param i32 i32) (result i32)
    local.get 0
    i32.load
    local.get 1
    i32.load
    i32.add))

;; function u0:0(i64 vmctx, i64, i32, i32) -> i32 tail {
;;     gv0 = vmctx
;;     gv1 = load.i64 notrap aligned readonly checked gv0+96
;;
;;                                 block0(v0: i64, v1: i64, v2: i32, v3: i32):
;; @0021                               v5 = uextend.i64 v2
;; @0021                               v6 = global_value.i64 gv1
;; @0021                               v7 = iadd v6, v5
;; @0021                               v8 = load.i32 little heap v7
;; @0026                               v9 = uextend.i64 v3
;; @0026                               v10 = global_value.i64 gv1
;; @0026                               v11 = iadd v10, v9
;; @0026                               v12 = load.i32 little heap v11
;; @0029                               v13 = iadd v8, v12
;; @002a                               jump block1(v13)
;;
;;                                 block1(v4: i32):
;; @002a                               return v4
;; }
