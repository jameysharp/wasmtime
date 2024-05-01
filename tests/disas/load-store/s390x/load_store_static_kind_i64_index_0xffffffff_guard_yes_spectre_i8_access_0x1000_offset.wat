;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation -W memory64 -O static-memory-forced -O static-memory-guard-size=4294967295 -O dynamic-memory-guard-size=4294967295"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i64 1)

  (func (export "do_store") (param i64 i32)
    local.get 0
    local.get 1
    i32.store8 offset=0x1000)

  (func (export "do_load") (param i64) (result i32)
    local.get 0
    i32.load8_u offset=0x1000))

;; wasm[0]::function[0]:
;;       stmg    %r13, %r15, 0x68(%r15)
;;       lgr     %r1, %r15
;;       aghi    %r15, -0xa0
;;       stg     %r1, 0(%r15)
;;       lghi    %r13, 0
;;       lgr     %r3, %r4
;;       ag      %r3, 0x60(%r2)
;;       aghi    %r3, 0x1000
;;       clgfi   %r4, 0xffffefff
;;       locgrh  %r3, %r13
;;       stc     %r5, 0(%r3)
;;       lmg     %r13, %r15, 0x108(%r15)
;;       br      %r14
;;
;; wasm[0]::function[1]:
;;       stmg    %r14, %r15, 0x70(%r15)
;;       lgr     %r1, %r15
;;       aghi    %r15, -0xa0
;;       stg     %r1, 0(%r15)
;;       lghi    %r5, 0
;;       lgr     %r3, %r4
;;       ag      %r3, 0x60(%r2)
;;       aghik   %r2, %r3, 0x1000
;;       clgfi   %r4, 0xffffefff
;;       locgrh  %r2, %r5
;;       llc     %r2, 0(%r2)
;;       lmg     %r14, %r15, 0x110(%r15)
;;       br      %r14
