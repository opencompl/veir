; ModuleID = 'fastntt.ll'
source_filename = "fastntt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @fastNTT(ptr noundef %0, i64 noundef %1, i64 noundef %2, ptr noundef %3, i64 noundef %4, i64 noundef %5) #0 {
  %7 = icmp ne i64 %4, 0
  br i1 %7, label %8, label %9

8:                                                ; preds = %6
  br label %10

9:                                                ; preds = %6
  br label %10

10:                                               ; preds = %9, %8
  %11 = phi i64 [ %1, %8 ], [ 2, %9 ]
  %12 = icmp ne i64 %4, 0
  br i1 %12, label %13, label %14

13:                                               ; preds = %10
  br label %16

14:                                               ; preds = %10
  %15 = sdiv i64 %5, 2
  br label %16

16:                                               ; preds = %14, %13
  %17 = phi i64 [ 1, %13 ], [ %15, %14 ]
  %18 = sdiv i64 %1, 2
  br label %19

19:                                               ; preds = %89, %16
  %.07 = phi i64 [ %11, %16 ], [ %81, %89 ]
  %.06 = phi i64 [ %17, %16 ], [ %88, %89 ]
  %.05 = phi i64 [ %18, %16 ], [ %74, %89 ]
  %.04 = phi i64 [ 0, %16 ], [ %90, %89 ]
  br label %20

20:                                               ; preds = %22, %19
  %.01 = phi i64 [ 0, %19 ], [ %24, %22 ]
  %.0 = phi i64 [ %1, %19 ], [ %23, %22 ]
  %21 = icmp sgt i64 %.0, 1
  br i1 %21, label %22, label %25

22:                                               ; preds = %20
  %23 = ashr i64 %.0, 1
  %24 = add nsw i64 %.01, 1
  br label %20, !llvm.loop !6

25:                                               ; preds = %20
  %26 = icmp slt i64 %.04, %.01
  br i1 %26, label %27, label %91

27:                                               ; preds = %25
  br label %28

28:                                               ; preds = %71, %27
  %.03 = phi i64 [ 0, %27 ], [ %72, %71 ]
  %29 = sdiv i64 %1, %.07
  %30 = icmp slt i64 %.03, %29
  br i1 %30, label %31, label %73

31:                                               ; preds = %28
  br label %32

32:                                               ; preds = %68, %31
  %.02 = phi i64 [ 0, %31 ], [ %69, %68 ]
  %33 = sdiv i64 %.07, 2
  %34 = icmp slt i64 %.02, %33
  br i1 %34, label %35, label %70

35:                                               ; preds = %32
  %36 = mul nsw i64 %.03, %.07
  %37 = add nsw i64 %36, %.02
  %38 = getelementptr inbounds i64, ptr %0, i64 %37
  %39 = load i64, ptr %38, align 8
  %40 = mul nsw i64 %.03, %.07
  %41 = add nsw i64 %40, %.02
  %42 = sdiv i64 %.07, 2
  %43 = add nsw i64 %41, %42
  %44 = getelementptr inbounds i64, ptr %0, i64 %43
  %45 = load i64, ptr %44, align 8
  %46 = mul nsw i64 2, %.02
  %47 = add nsw i64 %46, 1
  %48 = mul nsw i64 %47, %.05
  %49 = getelementptr inbounds i64, ptr %3, i64 %48
  %50 = load i64, ptr %49, align 8
  %51 = mul nsw i64 %50, %45
  %52 = srem i64 %51, %2
  %53 = add nsw i64 %39, %52
  %54 = srem i64 %53, %2
  %55 = mul nsw i64 %50, %45
  %56 = srem i64 %55, %2
  %57 = sub nsw i64 %39, %56
  %58 = add nsw i64 %57, %2
  %59 = srem i64 %58, %2
  %60 = mul nsw i64 %.03, %.07
  %61 = add nsw i64 %60, %.02
  %62 = getelementptr inbounds i64, ptr %0, i64 %61
  store i64 %54, ptr %62, align 8
  %63 = mul nsw i64 %.03, %.07
  %64 = add nsw i64 %63, %.02
  %65 = sdiv i64 %.07, 2
  %66 = add nsw i64 %64, %65
  %67 = getelementptr inbounds i64, ptr %0, i64 %66
  store i64 %59, ptr %67, align 8
  br label %68

68:                                               ; preds = %35
  %69 = add nsw i64 %.02, 1
  br label %32, !llvm.loop !8

70:                                               ; preds = %32
  br label %71

71:                                               ; preds = %70
  %72 = add nsw i64 %.03, 1
  br label %28, !llvm.loop !9

73:                                               ; preds = %28
  %74 = sdiv i64 %.05, 2
  %75 = icmp ne i64 %4, 0
  br i1 %75, label %76, label %78

76:                                               ; preds = %73
  %77 = sdiv i64 %.07, 2
  br label %80

78:                                               ; preds = %73
  %79 = mul nsw i64 %.07, 2
  br label %80

80:                                               ; preds = %78, %76
  %81 = phi i64 [ %77, %76 ], [ %79, %78 ]
  %82 = icmp ne i64 %4, 0
  br i1 %82, label %83, label %85

83:                                               ; preds = %80
  %84 = mul nsw i64 %.06, 2
  br label %87

85:                                               ; preds = %80
  %86 = sdiv i64 %.06, 2
  br label %87

87:                                               ; preds = %85, %83
  %88 = phi i64 [ %84, %83 ], [ %86, %85 ]
  br label %89

89:                                               ; preds = %87
  %90 = add nsw i64 %.04, 1
  br label %19, !llvm.loop !10

91:                                               ; preds = %25
  ret void
}

attributes #0 = { alwaysinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}
!10 = distinct !{!10, !7}
