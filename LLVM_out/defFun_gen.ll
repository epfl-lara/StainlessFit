define i32 @fac(i32 %n) {
  entry0:
    %local0 = icmp slt i32 %n, 1
    br i1 %local0, label %then0, label %else0

  then0:
    %local1 = add i32 0, 1
    br label %after0

  else0:
    br label %tempBlock0

  after0:
    %result0 = phi i32 [%local1, %then0],[%local2, %afterBlock0]
    br label %End0

  tempBlock0:
    br label %tempBlock1

  afterBlock0:
    %local2 = mul i32 %n, %local4
    br label %after0

  tempBlock1:
    %local5 = sub i32 %n, 1
    br label %afterBlock1

  afterBlock1:
    %local4 = call i32 @fac(i32 %local5)
    br label %afterBlock0

  End0:
    ret i32 %result0
}

define i32 @fibo(i32 %n) {
  entry0:
    %local0 = icmp eq i32 %n, 0
    br i1 %local0, label %then0, label %else0

  then0:
    %local1 = add i32 0, 0
    br label %after0

  else0:
    %local4 = icmp eq i32 %n, 1
    br i1 %local4, label %then1, label %else1

  after0:
    %result0 = phi i32 [%local1, %then0],[%local2, %after1]
    br label %End0

  then1:
    %local5 = add i32 0, 1
    br label %after1

  else1:
    br label %tempBlock0

  after1:
    %local2 = phi i32 [%local5, %then1],[%local6, %afterBlock2]
    br label %after0

  tempBlock0:
    br label %tempBlock1

  afterBlock0:
    br label %tempBlock2

  tempBlock1:
    %local10 = sub i32 %n, 1
    br label %afterBlock1

  afterBlock1:
    %local8 = call i32 @fibo(i32 %local10)
    br label %afterBlock0

  tempBlock2:
    br label %tempBlock3

  afterBlock2:
    %local6 = add i32 %local8, %local9
    br label %after1

  tempBlock3:
    %local11 = sub i32 %n, 2
    br label %afterBlock3

  afterBlock3:
    %local9 = call i32 @fibo(i32 %local11)
    br label %afterBlock2

  End0:
    ret i32 %result0
}

define i32 @main() {
  entry0:
    br label %tempBlock0

  tempBlock0:
    %local0 = call i32 @fac(i32 5)
    br label %afterBlock0

  afterBlock0:
    br label %tempBlock1

  tempBlock1:
    %local1 = call i32 @fibo(i32 10)
    br label %afterBlock1

  afterBlock1:
    %result0 = add i32 %local0, %local1
    br label %End0

  End0:
    ret i32 %result0
}