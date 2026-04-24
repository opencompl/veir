; ModuleID = 'fastntt.c'
source_filename = "fastntt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @log2FloorAux(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 %0, ptr %4, align 4
  store i32 %1, ptr %5, align 4
  %6 = load i32, ptr %4, align 4
  %7 = icmp eq i32 %6, 0
  br i1 %7, label %8, label %9

8:                                                ; preds = %2
  store i32 0, ptr %3, align 4
  br label %19

9:                                                ; preds = %2
  %10 = load i32, ptr %4, align 4
  %11 = icmp eq i32 %10, 1
  br i1 %11, label %12, label %13

12:                                               ; preds = %9
  store i32 0, ptr %3, align 4
  br label %19

13:                                               ; preds = %9
  %14 = load i32, ptr %4, align 4
  %15 = sdiv i32 %14, 2
  %16 = load i32, ptr %5, align 4
  %17 = add nsw i32 %16, 1
  %18 = call i32 @log2FloorAux(i32 noundef %15, i32 noundef %17)
  store i32 %18, ptr %3, align 4
  br label %19

19:                                               ; preds = %13, %12, %8
  %20 = load i32, ptr %3, align 4
  ret i32 %20
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @log2Floor(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = call i32 @log2FloorAux(i32 noundef %3, i32 noundef 0)
  ret i32 %4
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @bflyCT(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef %4, ptr noundef %5) #0 {
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca ptr, align 8
  %12 = alloca ptr, align 8
  store i32 %0, ptr %7, align 4
  store i32 %1, ptr %8, align 4
  store i32 %2, ptr %9, align 4
  store i32 %3, ptr %10, align 4
  store ptr %4, ptr %11, align 8
  store ptr %5, ptr %12, align 8
  %13 = load i32, ptr %7, align 4
  %14 = load i32, ptr %9, align 4
  %15 = load i32, ptr %8, align 4
  %16 = mul nsw i32 %14, %15
  %17 = load i32, ptr %10, align 4
  %18 = srem i32 %16, %17
  %19 = add nsw i32 %13, %18
  %20 = load i32, ptr %10, align 4
  %21 = srem i32 %19, %20
  %22 = load ptr, ptr %11, align 8
  store i32 %21, ptr %22, align 4
  %23 = load i32, ptr %7, align 4
  %24 = load i32, ptr %9, align 4
  %25 = load i32, ptr %8, align 4
  %26 = mul nsw i32 %24, %25
  %27 = load i32, ptr %10, align 4
  %28 = srem i32 %26, %27
  %29 = sub nsw i32 %23, %28
  %30 = load i32, ptr %10, align 4
  %31 = add nsw i32 %29, %30
  %32 = load i32, ptr %10, align 4
  %33 = srem i32 %31, %32
  %34 = load ptr, ptr %12, align 8
  store i32 %33, ptr %34, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @bflyGS(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef %4, ptr noundef %5) #0 {
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca ptr, align 8
  %12 = alloca ptr, align 8
  store i32 %0, ptr %7, align 4
  store i32 %1, ptr %8, align 4
  store i32 %2, ptr %9, align 4
  store i32 %3, ptr %10, align 4
  store ptr %4, ptr %11, align 8
  store ptr %5, ptr %12, align 8
  %13 = load i32, ptr %7, align 4
  %14 = load i32, ptr %8, align 4
  %15 = add nsw i32 %13, %14
  %16 = load i32, ptr %10, align 4
  %17 = srem i32 %15, %16
  %18 = load ptr, ptr %11, align 8
  store i32 %17, ptr %18, align 4
  %19 = load i32, ptr %7, align 4
  %20 = load i32, ptr %8, align 4
  %21 = sub nsw i32 %19, %20
  %22 = load i32, ptr %9, align 4
  %23 = mul nsw i32 %21, %22
  %24 = load i32, ptr %10, align 4
  %25 = srem i32 %23, %24
  %26 = load ptr, ptr %12, align 8
  store i32 %25, ptr %26, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fastNTT(ptr noundef %0, i32 noundef %1, i32 noundef %2, ptr noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = alloca ptr, align 8
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca ptr, align 8
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  %22 = alloca i32, align 4
  %23 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store i32 %1, ptr %8, align 4
  store i32 %2, ptr %9, align 4
  store ptr %3, ptr %10, align 8
  store i32 %4, ptr %11, align 4
  store i32 %5, ptr %12, align 4
  %24 = load i32, ptr %11, align 4
  %25 = icmp ne i32 %24, 0
  br i1 %25, label %26, label %28

26:                                               ; preds = %6
  %27 = load i32, ptr %8, align 4
  br label %29

28:                                               ; preds = %6
  br label %29

29:                                               ; preds = %28, %26
  %30 = phi i32 [ %27, %26 ], [ 2, %28 ]
  store i32 %30, ptr %13, align 4
  %31 = load i32, ptr %11, align 4
  %32 = icmp ne i32 %31, 0
  br i1 %32, label %33, label %34

33:                                               ; preds = %29
  br label %37

34:                                               ; preds = %29
  %35 = load i32, ptr %12, align 4
  %36 = sdiv i32 %35, 2
  br label %37

37:                                               ; preds = %34, %33
  %38 = phi i32 [ 1, %33 ], [ %36, %34 ]
  store i32 %38, ptr %14, align 4
  %39 = load i32, ptr %8, align 4
  %40 = sdiv i32 %39, 2
  store i32 %40, ptr %15, align 4
  store i32 0, ptr %16, align 4
  br label %41

41:                                               ; preds = %145, %37
  %42 = load i32, ptr %16, align 4
  %43 = load i32, ptr %8, align 4
  %44 = call i32 @log2Floor(i32 noundef %43)
  %45 = icmp slt i32 %42, %44
  br i1 %45, label %46, label %148

46:                                               ; preds = %41
  store i32 0, ptr %17, align 4
  br label %47

47:                                               ; preds = %119, %46
  %48 = load i32, ptr %17, align 4
  %49 = load i32, ptr %8, align 4
  %50 = load i32, ptr %13, align 4
  %51 = sdiv i32 %49, %50
  %52 = icmp slt i32 %48, %51
  br i1 %52, label %53, label %122

53:                                               ; preds = %47
  store i32 0, ptr %18, align 4
  br label %54

54:                                               ; preds = %115, %53
  %55 = load i32, ptr %18, align 4
  %56 = load i32, ptr %13, align 4
  %57 = sdiv i32 %56, 2
  %58 = icmp slt i32 %55, %57
  br i1 %58, label %59, label %118

59:                                               ; preds = %54
  %60 = load ptr, ptr %7, align 8
  %61 = load i32, ptr %17, align 4
  %62 = load i32, ptr %13, align 4
  %63 = mul nsw i32 %61, %62
  %64 = load i32, ptr %18, align 4
  %65 = add nsw i32 %63, %64
  %66 = sext i32 %65 to i64
  %67 = getelementptr inbounds i32, ptr %60, i64 %66
  %68 = load i32, ptr %67, align 4
  store i32 %68, ptr %19, align 4
  %69 = load ptr, ptr %7, align 8
  %70 = load i32, ptr %17, align 4
  %71 = load i32, ptr %13, align 4
  %72 = mul nsw i32 %70, %71
  %73 = load i32, ptr %18, align 4
  %74 = add nsw i32 %72, %73
  %75 = load i32, ptr %13, align 4
  %76 = sdiv i32 %75, 2
  %77 = add nsw i32 %74, %76
  %78 = sext i32 %77 to i64
  %79 = getelementptr inbounds i32, ptr %69, i64 %78
  %80 = load i32, ptr %79, align 4
  store i32 %80, ptr %20, align 4
  %81 = load ptr, ptr %10, align 8
  %82 = load i32, ptr %18, align 4
  %83 = mul nsw i32 2, %82
  %84 = add nsw i32 %83, 1
  %85 = load i32, ptr %15, align 4
  %86 = mul nsw i32 %84, %85
  %87 = sext i32 %86 to i64
  %88 = getelementptr inbounds i32, ptr %81, i64 %87
  %89 = load i32, ptr %88, align 4
  store i32 %89, ptr %21, align 4
  %90 = load i32, ptr %19, align 4
  %91 = load i32, ptr %20, align 4
  %92 = load i32, ptr %21, align 4
  %93 = load i32, ptr %9, align 4
  call void @bflyCT(i32 noundef %90, i32 noundef %91, i32 noundef %92, i32 noundef %93, ptr noundef %22, ptr noundef %23)
  %94 = load i32, ptr %22, align 4
  %95 = load ptr, ptr %7, align 8
  %96 = load i32, ptr %17, align 4
  %97 = load i32, ptr %13, align 4
  %98 = mul nsw i32 %96, %97
  %99 = load i32, ptr %18, align 4
  %100 = add nsw i32 %98, %99
  %101 = sext i32 %100 to i64
  %102 = getelementptr inbounds i32, ptr %95, i64 %101
  store i32 %94, ptr %102, align 4
  %103 = load i32, ptr %23, align 4
  %104 = load ptr, ptr %7, align 8
  %105 = load i32, ptr %17, align 4
  %106 = load i32, ptr %13, align 4
  %107 = mul nsw i32 %105, %106
  %108 = load i32, ptr %18, align 4
  %109 = add nsw i32 %107, %108
  %110 = load i32, ptr %13, align 4
  %111 = sdiv i32 %110, 2
  %112 = add nsw i32 %109, %111
  %113 = sext i32 %112 to i64
  %114 = getelementptr inbounds i32, ptr %104, i64 %113
  store i32 %103, ptr %114, align 4
  br label %115

115:                                              ; preds = %59
  %116 = load i32, ptr %18, align 4
  %117 = add nsw i32 %116, 1
  store i32 %117, ptr %18, align 4
  br label %54, !llvm.loop !6

118:                                              ; preds = %54
  br label %119

119:                                              ; preds = %118
  %120 = load i32, ptr %17, align 4
  %121 = add nsw i32 %120, 1
  store i32 %121, ptr %17, align 4
  br label %47, !llvm.loop !8

122:                                              ; preds = %47
  %123 = load i32, ptr %15, align 4
  %124 = sdiv i32 %123, 2
  store i32 %124, ptr %15, align 4
  %125 = load i32, ptr %11, align 4
  %126 = icmp ne i32 %125, 0
  br i1 %126, label %127, label %130

127:                                              ; preds = %122
  %128 = load i32, ptr %13, align 4
  %129 = sdiv i32 %128, 2
  br label %133

130:                                              ; preds = %122
  %131 = load i32, ptr %13, align 4
  %132 = mul nsw i32 %131, 2
  br label %133

133:                                              ; preds = %130, %127
  %134 = phi i32 [ %129, %127 ], [ %132, %130 ]
  store i32 %134, ptr %13, align 4
  %135 = load i32, ptr %11, align 4
  %136 = icmp ne i32 %135, 0
  br i1 %136, label %137, label %140

137:                                              ; preds = %133
  %138 = load i32, ptr %14, align 4
  %139 = mul nsw i32 %138, 2
  br label %143

140:                                              ; preds = %133
  %141 = load i32, ptr %14, align 4
  %142 = sdiv i32 %141, 2
  br label %143

143:                                              ; preds = %140, %137
  %144 = phi i32 [ %139, %137 ], [ %142, %140 ]
  store i32 %144, ptr %14, align 4
  br label %145

145:                                              ; preds = %143
  %146 = load i32, ptr %16, align 4
  %147 = add nsw i32 %146, 1
  store i32 %147, ptr %16, align 4
  br label %41, !llvm.loop !9

148:                                              ; preds = %41
  ret void
}

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

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
