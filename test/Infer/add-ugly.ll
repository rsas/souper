; REQUIRES: solver
; RUN: llvm-as %s -o - | %souper %solver -souper-infer-inst -souper-exploit-blockpcs -souper-synthesis-comps=add,and > %t2
; RUN: FileCheck %s < %t2
; CHECK: cand %10 %12

; stupid 2-bit number increment

; ModuleID = 'inc.bc'
source_filename = "add-small.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

; Function Attrs: nounwind readnone ssp uwtable
define i32 @inc_ugly(i32) local_unnamed_addr #0 {
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

; <label>:12:                                     ; preds = %10, %7, %4
  %13 = phi i32 [ %11, %10 ], [ %9, %7 ], [ 0, %4 ]
  %14 = and i32 %13, 3
  ret i32 %14
}

attributes #0 = { nounwind readnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 5.0.1 (branches/release_50 314818)"}
