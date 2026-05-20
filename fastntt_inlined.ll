; ModuleID = 'fastntt.ll'
source_filename = "fastntt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: alwaysinline nounwind uwtable
define dso_local i32 @log2FloorAux(i32 noundef %0) #0 {
  br label %2

2:                                                ; preds = %4, %1
  %.01 = phi i32 [ 0, %1 ], [ %6, %4 ]
  %.0 = phi i32 [ %0, %1 ], [ %5, %4 ]
  %3 = icmp sgt i32 %.0, 1
  br i1 %3, label %4, label %7

4:                                                ; preds = %2
  %5 = ashr i32 %.0, 1
  %6 = add nsw i32 %.01, 1
  br label %2, !llvm.loop !6

7:                                                ; preds = %2
  ret i32 %.01
}

; Function Attrs: alwaysinline nounwind uwtable
define dso_local i32 @log2Floor(i32 noundef %0) #0 {
  br label %2

2:                                                ; preds = %4, %1
  %.01 = phi i32 [ 0, %1 ], [ %6, %4 ]
  %.0 = phi i32 [ %0, %1 ], [ %5, %4 ]
  %3 = icmp sgt i32 %.0, 1
  br i1 %3, label %4, label %7

4:                                                ; preds = %2
  %5 = ashr i32 %.0, 1
  %6 = add nsw i32 %.01, 1
  br label %2, !llvm.loop !6

7:                                                ; preds = %2
  ret i32 %.01
}

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @bflyCT(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef %4, ptr noundef %5) #0 {
  %7 = mul nsw i32 %2, %1
  %8 = srem i32 %7, %3
  %9 = add nsw i32 %0, %8
  %10 = srem i32 %9, %3
  store i32 %10, ptr %4, align 4
  %11 = mul nsw i32 %2, %1
  %12 = srem i32 %11, %3
  %13 = sub nsw i32 %0, %12
  %14 = add nsw i32 %13, %3
  %15 = srem i32 %14, %3
  store i32 %15, ptr %5, align 4
  ret void
}

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @bflyGS(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef %4, ptr noundef %5) #0 {
  %7 = add nsw i32 %0, %1
  %8 = srem i32 %7, %3
  store i32 %8, ptr %4, align 4
  %9 = sub nsw i32 %0, %1
  %10 = mul nsw i32 %9, %2
  %11 = srem i32 %10, %3
  store i32 %11, ptr %5, align 4
  ret void
}

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @fastNTT(ptr noundef %0, i32 noundef %1, i32 noundef %2, ptr noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = icmp ne i32 %4, 0
  br i1 %7, label %8, label %9

8:                                                ; preds = %6
  br label %10

9:                                                ; preds = %6
  br label %10

10:                                               ; preds = %9, %8
  %11 = phi i32 [ %1, %8 ], [ 2, %9 ]
  %12 = icmp ne i32 %4, 0
  br i1 %12, label %13, label %14

13:                                               ; preds = %10
  br label %16

14:                                               ; preds = %10
  %15 = sdiv i32 %5, 2
  br label %16

16:                                               ; preds = %14, %13
  %17 = phi i32 [ 1, %13 ], [ %15, %14 ]
  %18 = sdiv i32 %1, 2
  br label %19

19:                                               ; preds = %94, %16
  %.05 = phi i32 [ %11, %16 ], [ %86, %94 ]
  %.04 = phi i32 [ %17, %16 ], [ %93, %94 ]
  %.03 = phi i32 [ %18, %16 ], [ %79, %94 ]
  %.02 = phi i32 [ 0, %16 ], [ %95, %94 ]
  br label %20

20:                                               ; preds = %22, %19
  %.07 = phi i32 [ 0, %19 ], [ %24, %22 ]
  %.06 = phi i32 [ %1, %19 ], [ %23, %22 ]
  %21 = icmp sgt i32 %.06, 1
  br i1 %21, label %22, label %25

22:                                               ; preds = %20
  %23 = ashr i32 %.06, 1
  %24 = add nsw i32 %.07, 1
  br label %20, !llvm.loop !6

25:                                               ; preds = %20
  %26 = icmp slt i32 %.02, %.07
  br i1 %26, label %27, label %96

27:                                               ; preds = %25
  br label %28

28:                                               ; preds = %76, %27
  %.01 = phi i32 [ 0, %27 ], [ %77, %76 ]
  %29 = sdiv i32 %1, %.05
  %30 = icmp slt i32 %.01, %29
  br i1 %30, label %31, label %78

31:                                               ; preds = %28
  br label %32

32:                                               ; preds = %73, %31
  %.0 = phi i32 [ 0, %31 ], [ %74, %73 ]
  %33 = sdiv i32 %.05, 2
  %34 = icmp slt i32 %.0, %33
  br i1 %34, label %35, label %75

35:                                               ; preds = %32
  %36 = mul nsw i32 %.01, %.05
  %37 = add nsw i32 %36, %.0
  %38 = sext i32 %37 to i64
  %39 = getelementptr inbounds i32, ptr %0, i64 %38
  %40 = load i32, ptr %39, align 4
  %41 = mul nsw i32 %.01, %.05
  %42 = add nsw i32 %41, %.0
  %43 = sdiv i32 %.05, 2
  %44 = add nsw i32 %42, %43
  %45 = sext i32 %44 to i64
  %46 = getelementptr inbounds i32, ptr %0, i64 %45
  %47 = load i32, ptr %46, align 4
  %48 = mul nsw i32 2, %.0
  %49 = add nsw i32 %48, 1
  %50 = mul nsw i32 %49, %.03
  %51 = sext i32 %50 to i64
  %52 = getelementptr inbounds i32, ptr %3, i64 %51
  %53 = load i32, ptr %52, align 4
  %54 = mul nsw i32 %53, %47
  %55 = srem i32 %54, %2
  %56 = add nsw i32 %40, %55
  %57 = srem i32 %56, %2
  %58 = mul nsw i32 %53, %47
  %59 = srem i32 %58, %2
  %60 = sub nsw i32 %40, %59
  %61 = add nsw i32 %60, %2
  %62 = srem i32 %61, %2
  %63 = mul nsw i32 %.01, %.05
  %64 = add nsw i32 %63, %.0
  %65 = sext i32 %64 to i64
  %66 = getelementptr inbounds i32, ptr %0, i64 %65
  store i32 %57, ptr %66, align 4
  %67 = mul nsw i32 %.01, %.05
  %68 = add nsw i32 %67, %.0
  %69 = sdiv i32 %.05, 2
  %70 = add nsw i32 %68, %69
  %71 = sext i32 %70 to i64
  %72 = getelementptr inbounds i32, ptr %0, i64 %71
  store i32 %62, ptr %72, align 4
  br label %73

73:                                               ; preds = %35
  %74 = add nsw i32 %.0, 1
  br label %32, !llvm.loop !8

75:                                               ; preds = %32
  br label %76

76:                                               ; preds = %75
  %77 = add nsw i32 %.01, 1
  br label %28, !llvm.loop !9

78:                                               ; preds = %28
  %79 = sdiv i32 %.03, 2
  %80 = icmp ne i32 %4, 0
  br i1 %80, label %81, label %83

81:                                               ; preds = %78
  %82 = sdiv i32 %.05, 2
  br label %85

83:                                               ; preds = %78
  %84 = mul nsw i32 %.05, 2
  br label %85

85:                                               ; preds = %83, %81
  %86 = phi i32 [ %82, %81 ], [ %84, %83 ]
  %87 = icmp ne i32 %4, 0
  br i1 %87, label %88, label %90

88:                                               ; preds = %85
  %89 = mul nsw i32 %.04, 2
  br label %92

90:                                               ; preds = %85
  %91 = sdiv i32 %.04, 2
  br label %92

92:                                               ; preds = %90, %88
  %93 = phi i32 [ %89, %88 ], [ %91, %90 ]
  br label %94

94:                                               ; preds = %92
  %95 = add nsw i32 %.02, 1
  br label %19, !llvm.loop !10

96:                                               ; preds = %25
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
