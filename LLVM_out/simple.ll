; Main function
define i32 @main(i32 %arg, i8** %arg1){
  entry0:
    %2 = true
    br %2, %then0, %else0
    %0 = false
    %1 = false
    %result0 = phi TYPE [%0, %then0],[%1, %else0]
    ret i32 %result0
  then0:

  else0:

}