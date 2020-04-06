; ModuleID = 'LLVM_out/fibo_gen.ll'
source_filename = "LLVM_out/fibo_gen.ll"

; Function Attrs: nounwind readnone
define i32 @fibo(i32 %n) local_unnamed_addr #0 {
entry0:
  switch i32 %n, label %tempBlock1 [
    i32 0, label %End0
    i32 1, label %then1
  ]

then1:                                            ; preds = %entry0
  br label %End0

tempBlock1:                                       ; preds = %entry0
  %local10 = add i32 %n, -1
  %local8 = tail call i32 @fibo(i32 %local10)
  %local11 = add i32 %n, -2
  %local9 = tail call i32 @fibo(i32 %local11)
  %local6 = add i32 %local9, %local8
  ret i32 %local6

End0:                                             ; preds = %entry0, %then1
  %result0 = phi i32 [ 1, %then1 ], [ %n, %entry0 ]
  ret i32 %result0
}

; Function Attrs: nounwind readnone
define i32 @main() local_unnamed_addr #0 {
entry0:
  %result0 = tail call i32 @fibo(i32 10)
  ret i32 %result0
}

attributes #0 = { nounwind readnone }
