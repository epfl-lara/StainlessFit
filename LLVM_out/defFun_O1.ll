; ModuleID = 'LLVM_out/defFun_gen.ll'
source_filename = "LLVM_out/defFun_gen.ll"

; Function Attrs: nounwind readnone
define i32 @fac(i32 %n) local_unnamed_addr #0 {
entry0:
  %local01 = icmp slt i32 %n, 1
  br i1 %local01, label %End0, label %tempBlock1

tempBlock1:                                       ; preds = %entry0, %tempBlock1
  %n.tr3 = phi i32 [ %local5, %tempBlock1 ], [ %n, %entry0 ]
  %accumulator.tr2 = phi i32 [ %local2, %tempBlock1 ], [ 1, %entry0 ]
  %local5 = add nsw i32 %n.tr3, -1
  %local2 = mul i32 %n.tr3, %accumulator.tr2
  %local0 = icmp slt i32 %n.tr3, 2
  br i1 %local0, label %End0, label %tempBlock1

End0:                                             ; preds = %tempBlock1, %entry0
  %accumulator.tr.lcssa = phi i32 [ 1, %entry0 ], [ %local2, %tempBlock1 ]
  ret i32 %accumulator.tr.lcssa
}

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
  %local0 = tail call i32 @fac(i32 5)
  %local1 = tail call i32 @fibo(i32 10)
  %result0 = add i32 %local1, %local0
  ret i32 %result0
}

attributes #0 = { nounwind readnone }
