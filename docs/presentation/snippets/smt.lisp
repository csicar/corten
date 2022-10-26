; checking is_sub_context ...
(declare-datatypes () ((Unit unit)))
(declare-const |_0| Int)
(declare-const |r| Int)
(declare-const |a1| Int)
(declare-const |b1| Int)
(declare-const |a2| Int)

; ty!{ r : i32 | (r <= b1) }
(assert (<= |r| |b1|))

; ty!{ a1 : &mut i32 | true }
(assert true)

;     ty!{ b1 : i32 | true }
(assert true)

; SuperCtx:
(assert (not (and
        (<= |r| |b1|)
        true
    )))

; checking: RContext {
;     a : ty!{ _0 : &mut i32 | _0 == & arg (0usize) }
;     <dangling> : ty!{ a1 : &mut i32 | true }
;     b : ty!{ b1 : i32 | true }
;     <argument 0> : ty!{ r : i32 | (r <= b1) }
; }
;  <: RContext {
;     <argument 0> : ty!{ a2 : &mut i32 | a2 <= b1 }
;     b : ty!{ b1 : i32 | true }
; }
(check-sat)