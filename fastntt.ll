; ModuleID = 'fastntt.c'
source_filename = "fastntt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: alwaysinline nounwind uwtable
define dso_local i32 @log2FloorAux(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  store i32 0, ptr %3, align 4
  br label %4

4:                                                ; preds = %7, %1
  %5 = load i32, ptr %2, align 4
  %6 = icmp sgt i32 %5, 1
  br i1 %6, label %7, label %12

7:                                                ; preds = %4
  %8 = load i32, ptr %2, align 4
  %9 = ashr i32 %8, 1
  store i32 %9, ptr %2, align 4
  %10 = load i32, ptr %3, align 4
  %11 = add nsw i32 %10, 1
  store i32 %11, ptr %3, align 4
  br label %4, !llvm.loop !6

12:                                               ; preds = %4
  %13 = load i32, ptr %3, align 4
  ret i32 %13
}

; Function Attrs: alwaysinline nounwind uwtable
define dso_local i32 @log2Floor(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, ptr %4, align 4
  %5 = load i32, ptr %4, align 4
  store i32 %5, ptr %2, align 4
  store i32 0, ptr %3, align 4
  br label %6

6:                                                ; preds = %9, %1
  %7 = load i32, ptr %2, align 4
  %8 = icmp sgt i32 %7, 1
  br i1 %8, label %9, label %14

9:                                                ; preds = %6
  %10 = load i32, ptr %2, align 4
  %11 = ashr i32 %10, 1
  store i32 %11, ptr %2, align 4
  %12 = load i32, ptr %3, align 4
  %13 = add nsw i32 %12, 1
  store i32 %13, ptr %3, align 4
  br label %6, !llvm.loop !6

14:                                               ; preds = %6
  %15 = load i32, ptr %3, align 4
  ret i32 %15
}

; Function Attrs: alwaysinline nounwind uwtable
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

; Function Attrs: alwaysinline nounwind uwtable
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

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @fastNTT(ptr noundef %0, i32 noundef %1, i32 noundef %2, ptr noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca ptr, align 8
  %12 = alloca ptr, align 8
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca ptr, align 8
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca ptr, align 8
  %20 = alloca i32, align 4
  %21 = alloca i32, align 4
  %22 = alloca i32, align 4
  %23 = alloca i32, align 4
  %24 = alloca i32, align 4
  %25 = alloca i32, align 4
  %26 = alloca i32, align 4
  %27 = alloca i32, align 4
  %28 = alloca i32, align 4
  %29 = alloca i32, align 4
  %30 = alloca i32, align 4
  %31 = alloca i32, align 4
  %32 = alloca i32, align 4
  store ptr %0, ptr %16, align 8
  store i32 %1, ptr %17, align 4
  store i32 %2, ptr %18, align 4
  store ptr %3, ptr %19, align 8
  store i32 %4, ptr %20, align 4
  store i32 %5, ptr %21, align 4
  %33 = load i32, ptr %20, align 4
  %34 = icmp ne i32 %33, 0
  br i1 %34, label %35, label %37

35:                                               ; preds = %6
  %36 = load i32, ptr %17, align 4
  br label %38

37:                                               ; preds = %6
  br label %38

38:                                               ; preds = %37, %35
  %39 = phi i32 [ %36, %35 ], [ 2, %37 ]
  store i32 %39, ptr %22, align 4
  %40 = load i32, ptr %20, align 4
  %41 = icmp ne i32 %40, 0
  br i1 %41, label %42, label %43

42:                                               ; preds = %38
  br label %46

43:                                               ; preds = %38
  %44 = load i32, ptr %21, align 4
  %45 = sdiv i32 %44, 2
  br label %46

46:                                               ; preds = %43, %42
  %47 = phi i32 [ 1, %42 ], [ %45, %43 ]
  store i32 %47, ptr %23, align 4
  %48 = load i32, ptr %17, align 4
  %49 = sdiv i32 %48, 2
  store i32 %49, ptr %24, align 4
  store i32 0, ptr %25, align 4
  br label %50

50:                                               ; preds = %186, %46
  %51 = load i32, ptr %25, align 4
  %52 = load i32, ptr %17, align 4
  store i32 %52, ptr %15, align 4
  %53 = load i32, ptr %15, align 4
  store i32 %53, ptr %13, align 4
  store i32 0, ptr %14, align 4
  br label %54

54:                                               ; preds = %57, %50
  %55 = load i32, ptr %13, align 4
  %56 = icmp sgt i32 %55, 1
  br i1 %56, label %57, label %62

57:                                               ; preds = %54
  %58 = load i32, ptr %13, align 4
  %59 = ashr i32 %58, 1
  store i32 %59, ptr %13, align 4
  %60 = load i32, ptr %14, align 4
  %61 = add nsw i32 %60, 1
  store i32 %61, ptr %14, align 4
  br label %54, !llvm.loop !6

62:                                               ; preds = %54
  %63 = load i32, ptr %14, align 4
  %64 = icmp slt i32 %51, %63
  br i1 %64, label %65, label %189

65:                                               ; preds = %62
  store i32 0, ptr %26, align 4
  br label %66

66:                                               ; preds = %160, %65
  %67 = load i32, ptr %26, align 4
  %68 = load i32, ptr %17, align 4
  %69 = load i32, ptr %22, align 4
  %70 = sdiv i32 %68, %69
  %71 = icmp slt i32 %67, %70
  br i1 %71, label %72, label %163

72:                                               ; preds = %66
  store i32 0, ptr %27, align 4
  br label %73

73:                                               ; preds = %156, %72
  %74 = load i32, ptr %27, align 4
  %75 = load i32, ptr %22, align 4
  %76 = sdiv i32 %75, 2
  %77 = icmp slt i32 %74, %76
  br i1 %77, label %78, label %159

78:                                               ; preds = %73
  %79 = load ptr, ptr %16, align 8
  %80 = load i32, ptr %26, align 4
  %81 = load i32, ptr %22, align 4
  %82 = mul nsw i32 %80, %81
  %83 = load i32, ptr %27, align 4
  %84 = add nsw i32 %82, %83
  %85 = sext i32 %84 to i64
  %86 = getelementptr inbounds i32, ptr %79, i64 %85
  %87 = load i32, ptr %86, align 4
  store i32 %87, ptr %28, align 4
  %88 = load ptr, ptr %16, align 8
  %89 = load i32, ptr %26, align 4
  %90 = load i32, ptr %22, align 4
  %91 = mul nsw i32 %89, %90
  %92 = load i32, ptr %27, align 4
  %93 = add nsw i32 %91, %92
  %94 = load i32, ptr %22, align 4
  %95 = sdiv i32 %94, 2
  %96 = add nsw i32 %93, %95
  %97 = sext i32 %96 to i64
  %98 = getelementptr inbounds i32, ptr %88, i64 %97
  %99 = load i32, ptr %98, align 4
  store i32 %99, ptr %29, align 4
  %100 = load ptr, ptr %19, align 8
  %101 = load i32, ptr %27, align 4
  %102 = mul nsw i32 2, %101
  %103 = add nsw i32 %102, 1
  %104 = load i32, ptr %24, align 4
  %105 = mul nsw i32 %103, %104
  %106 = sext i32 %105 to i64
  %107 = getelementptr inbounds i32, ptr %100, i64 %106
  %108 = load i32, ptr %107, align 4
  store i32 %108, ptr %30, align 4
  %109 = load i32, ptr %28, align 4
  %110 = load i32, ptr %29, align 4
  %111 = load i32, ptr %30, align 4
  %112 = load i32, ptr %18, align 4
  store i32 %109, ptr %7, align 4
  store i32 %110, ptr %8, align 4
  store i32 %111, ptr %9, align 4
  store i32 %112, ptr %10, align 4
  store ptr %31, ptr %11, align 8
  store ptr %32, ptr %12, align 8
  %113 = load i32, ptr %7, align 4
  %114 = load i32, ptr %9, align 4
  %115 = load i32, ptr %8, align 4
  %116 = mul nsw i32 %114, %115
  %117 = load i32, ptr %10, align 4
  %118 = srem i32 %116, %117
  %119 = add nsw i32 %113, %118
  %120 = load i32, ptr %10, align 4
  %121 = srem i32 %119, %120
  %122 = load ptr, ptr %11, align 8
  store i32 %121, ptr %122, align 4
  %123 = load i32, ptr %7, align 4
  %124 = load i32, ptr %9, align 4
  %125 = load i32, ptr %8, align 4
  %126 = mul nsw i32 %124, %125
  %127 = load i32, ptr %10, align 4
  %128 = srem i32 %126, %127
  %129 = sub nsw i32 %123, %128
  %130 = load i32, ptr %10, align 4
  %131 = add nsw i32 %129, %130
  %132 = load i32, ptr %10, align 4
  %133 = srem i32 %131, %132
  %134 = load ptr, ptr %12, align 8
  store i32 %133, ptr %134, align 4
  %135 = load i32, ptr %31, align 4
  %136 = load ptr, ptr %16, align 8
  %137 = load i32, ptr %26, align 4
  %138 = load i32, ptr %22, align 4
  %139 = mul nsw i32 %137, %138
  %140 = load i32, ptr %27, align 4
  %141 = add nsw i32 %139, %140
  %142 = sext i32 %141 to i64
  %143 = getelementptr inbounds i32, ptr %136, i64 %142
  store i32 %135, ptr %143, align 4
  %144 = load i32, ptr %32, align 4
  %145 = load ptr, ptr %16, align 8
  %146 = load i32, ptr %26, align 4
  %147 = load i32, ptr %22, align 4
  %148 = mul nsw i32 %146, %147
  %149 = load i32, ptr %27, align 4
  %150 = add nsw i32 %148, %149
  %151 = load i32, ptr %22, align 4
  %152 = sdiv i32 %151, 2
  %153 = add nsw i32 %150, %152
  %154 = sext i32 %153 to i64
  %155 = getelementptr inbounds i32, ptr %145, i64 %154
  store i32 %144, ptr %155, align 4
  br label %156

156:                                              ; preds = %78
  %157 = load i32, ptr %27, align 4
  %158 = add nsw i32 %157, 1
  store i32 %158, ptr %27, align 4
  br label %73, !llvm.loop !8

159:                                              ; preds = %73
  br label %160

160:                                              ; preds = %159
  %161 = load i32, ptr %26, align 4
  %162 = add nsw i32 %161, 1
  store i32 %162, ptr %26, align 4
  br label %66, !llvm.loop !9

163:                                              ; preds = %66
  %164 = load i32, ptr %24, align 4
  %165 = sdiv i32 %164, 2
  store i32 %165, ptr %24, align 4
  %166 = load i32, ptr %20, align 4
  %167 = icmp ne i32 %166, 0
  br i1 %167, label %168, label %171

168:                                              ; preds = %163
  %169 = load i32, ptr %22, align 4
  %170 = sdiv i32 %169, 2
  br label %174

171:                                              ; preds = %163
  %172 = load i32, ptr %22, align 4
  %173 = mul nsw i32 %172, 2
  br label %174

174:                                              ; preds = %171, %168
  %175 = phi i32 [ %170, %168 ], [ %173, %171 ]
  store i32 %175, ptr %22, align 4
  %176 = load i32, ptr %20, align 4
  %177 = icmp ne i32 %176, 0
  br i1 %177, label %178, label %181

178:                                              ; preds = %174
  %179 = load i32, ptr %23, align 4
  %180 = mul nsw i32 %179, 2
  br label %184

181:                                              ; preds = %174
  %182 = load i32, ptr %23, align 4
  %183 = sdiv i32 %182, 2
  br label %184

184:                                              ; preds = %181, %178
  %185 = phi i32 [ %180, %178 ], [ %183, %181 ]
  store i32 %185, ptr %23, align 4
  br label %186

186:                                              ; preds = %184
  %187 = load i32, ptr %25, align 4
  %188 = add nsw i32 %187, 1
  store i32 %188, ptr %25, align 4
  br label %50, !llvm.loop !10

189:                                              ; preds = %62
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
