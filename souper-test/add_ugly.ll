
define i32 @add_ugly(i32) local_unnamed_addr #0 {
  %2 = and i32 %0, 1
  %3 = icmp eq i32 %2, 0
  br i1 %3, label %10, label %4

; <label>:4:                                      ; preds = %1
  %5 = and i32 %0, 2
  %6 = icmp eq i32 %5, 0
  br i1 %6, label %7, label %12

; <label>:7:                                      ; preds = %4
  %8 = and i32 %0, -4
  %9 = or i32 %8, 2
  br label %12

; <label>:10:                                     ; preds = %1
  %11 = or i32 %0, 1
  br label %12

; <label>:12:                                     ; preds = %4, %7, %10
  %13 = phi i32 [ %11, %10 ], [ %9, %7 ], [ 0, %4 ]
  %14 = and i32 %13, 3
  ret i32 %14
}
