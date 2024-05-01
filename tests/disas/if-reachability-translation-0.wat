;;! target = "x86_64"

;; An unreachable `if` means that the consequent, alternative, and following
;; block are also unreachable.

(module
  (func (param i32) (result i32)
    unreachable
    if  ;; label = @2
      nop
    else
      nop
    end
    i32.const 0))

;; function u0:0(i64 vmctx, i64, i32) -> i32 tail {
;;                                 block0(v0: i64, v1: i64, v2: i32):
;; @0019                               trap unreachable
;; }
