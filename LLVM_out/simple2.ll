; Main function
define i1 @main(i32 %arg, i8** %arg1){
  entry0:
    %local0 = or i1 0, false
    br i1 %local0, label %then0, label %else0

  then0:
    %local4 = or i1 0, false
    br i1 %local4, label %then1, label %else1

  else0:
    %local8 = or i1 0, true
    br i1 %local8, label %then2, label %else2

  after0:
    %result0 = phi i1 [%local1, %after1],[%local2, %after2]
    br label %End0

  then1:
    %local5 = or i1 0, false
    br label %after1

  else1:
    %local6 = or i1 0, false
    br label %after1

  after1:
    %local1 = phi i1 [%local5, %then1],[%local6, %else1]
    br label %after0

  then2:
    %local9 = or i1 0, true
    br label %after2

  else2:
    %local10 = or i1 0, false
    br label %after2

  after2:
    %local2 = phi i1 [%local9, %then2],[%local10, %else2]
    br label %after0

  End0:
    ret i1 %result0
}