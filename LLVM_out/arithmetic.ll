define i32 @main() {
  entry0:
    %temp0 = and i1 true, false
    %local0 = and i1 %temp0, false
    br i1 %local0, label %then0, label %else0

  then0:
    %local1 = add i32 1, 2
    br label %after0

  else0:
    br label %tempBlock0

  after0:
    %result0 = phi i32 [%local1, %then0],[%local2, %after1]
    br label %End0

  then1:
    %local5 = add i32 0, 0
    br label %after1

  else1:
    %local6 = add i32 0, 5
    br label %after1

  after1:
    %local2 = phi i32 [%local5, %then1],[%local6, %else1]
    br label %after0

  tempBlock0:
    %local8 = mul i32 2, 4
    br label %afterBlock0

  afterBlock0:
    %local4 = icmp slt i32 2, %local8
    br i1 %local4, label %then1, label %else1

  End0:
    ret i32 %result0
}