; Leading comment
define i32 @commented(i32 %x) { ; trailing comment
entry: ; label comment
  ; full-line comment inside block
  %r = or i32 %x, 0 ; or with zero
  ret i32 %r ; done
}
; Final comment
