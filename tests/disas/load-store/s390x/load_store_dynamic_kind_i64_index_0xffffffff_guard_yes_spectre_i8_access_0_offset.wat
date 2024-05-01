;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation -W memory64 -O static-memory-maximum-size=0 -O static-memory-guard-size=4294967295 -O dynamic-memory-guard-size=4294967295"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i64 1)

  (func (export "do_store") (param i64 i32)
    local.get 0
    local.get 1
    i32.store8 offset=0)

  (func (export "do_load") (param i64) (result i32)
    local.get 0
    i32.load8_u offset=0))

;; wasm[0]::function[0]:
;;       stmg    %r12, %r15, 0x60(%r15)
;;       lgr     %r1, %r15
;;       aghi    %r15, -0xa0
;;       stg     %r1, 0(%r15)
;;       lg      %r13, 0x68(%r2)
;;       lghi    %r3, 0
;;       lgr     %r12, %r4
;;       ag      %r12, 0x60(%r2)
;;       clgr    %r4, %r13
;;       locgrhe %r12, %r3
;;       stc     %r5, 0(%r12)
;;       lmg     %r12, %r15, 0x100(%r15)
;;       br      %r14
;;
;; wasm[0]::function[1]:
;;       stmg    %r12, %r15, 0x60(%r15)
;;       lgr     %r1, %r15
;;       aghi    %r15, -0xa0
;;       stg     %r1, 0(%r15)
;;       lg      %r3, 0x68(%r2)
;;       lghi    %r5, 0
;;       lgr     %r12, %r4
;;       ag      %r12, 0x60(%r2)
;;       clgr    %r4, %r3
;;       locgrhe %r12, %r5
;;       llc     %r2, 0(%r12)
;;       lmg     %r12, %r15, 0x100(%r15)
;;       br      %r14
