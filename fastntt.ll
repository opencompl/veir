; ModuleID = 'fastntt.c'
source_filename = "fastntt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: alwaysinline nounwind uwtable
define dso_local void @fastNTT(ptr noundef %0, i64 noundef %1, i64 noundef %2, ptr noundef %3, i64 noundef %4, i64 noundef %5) #0 {
  %7 = alloca i64, align 8
  %8 = alloca i64, align 8
  %9 = alloca i64, align 8
  %10 = alloca i64, align 8
  %11 = alloca i64, align 8
  %12 = alloca i64, align 8
  %13 = alloca ptr, align 8
  %14 = alloca ptr, align 8
  %15 = alloca i64, align 8
  %16 = alloca ptr, align 8
  %17 = alloca i64, align 8
  %18 = alloca i64, align 8
  %19 = alloca ptr, align 8
  %20 = alloca i64, align 8
  %21 = alloca i64, align 8
  %22 = alloca i64, align 8
  %23 = alloca i64, align 8
  %24 = alloca i64, align 8
  %25 = alloca i64, align 8
  %26 = alloca i64, align 8
  %27 = alloca i64, align 8
  %28 = alloca i64, align 8
  %29 = alloca i64, align 8
  %30 = alloca i64, align 8
  %31 = alloca i64, align 8
  %32 = alloca i64, align 8
  store ptr %0, ptr %16, align 8
  store i64 %1, ptr %17, align 8
  store i64 %2, ptr %18, align 8
  store ptr %3, ptr %19, align 8
  store i64 %4, ptr %20, align 8
  store i64 %5, ptr %21, align 8
  %33 = load i64, ptr %20, align 8
  %34 = icmp ne i64 %33, 0
  br i1 %34, label %35, label %37

35:                                               ; preds = %6
  %36 = load i64, ptr %17, align 8
  br label %38

37:                                               ; preds = %6
  br label %38

38:                                               ; preds = %37, %35
  %39 = phi i64 [ %36, %35 ], [ 2, %37 ]
  store i64 %39, ptr %22, align 8
  %40 = load i64, ptr %20, align 8
  %41 = icmp ne i64 %40, 0
  br i1 %41, label %42, label %43

42:                                               ; preds = %38
  br label %46

43:                                               ; preds = %38
  %44 = load i64, ptr %21, align 8
  %45 = sdiv i64 %44, 2
  br label %46

46:                                               ; preds = %43, %42
  %47 = phi i64 [ 1, %42 ], [ %45, %43 ]
  store i64 %47, ptr %23, align 8
  %48 = load i64, ptr %17, align 8
  %49 = sdiv i64 %48, 2
  store i64 %49, ptr %24, align 8
  store i64 0, ptr %25, align 8
  br label %50

50:                                               ; preds = %181, %46
  %51 = load i64, ptr %25, align 8
  %52 = load i64, ptr %17, align 8
  store i64 %52, ptr %15, align 8
  %53 = load i64, ptr %15, align 8
  store i64 %53, ptr %7, align 8
  store i64 0, ptr %8, align 8
  br label %54

54:                                               ; preds = %57, %50
  %55 = load i64, ptr %7, align 8
  %56 = icmp sgt i64 %55, 1
  br i1 %56, label %57, label %62

57:                                               ; preds = %54
  %58 = load i64, ptr %7, align 8
  %59 = ashr i64 %58, 1
  store i64 %59, ptr %7, align 8
  %60 = load i64, ptr %8, align 8
  %61 = add nsw i64 %60, 1
  store i64 %61, ptr %8, align 8
  br label %54, !llvm.loop !6

62:                                               ; preds = %54
  %63 = load i64, ptr %8, align 8
  %64 = icmp slt i64 %51, %63
  br i1 %64, label %65, label %184

65:                                               ; preds = %62
  store i64 0, ptr %26, align 8
  br label %66

66:                                               ; preds = %155, %65
  %67 = load i64, ptr %26, align 8
  %68 = load i64, ptr %17, align 8
  %69 = load i64, ptr %22, align 8
  %70 = sdiv i64 %68, %69
  %71 = icmp slt i64 %67, %70
  br i1 %71, label %72, label %158

72:                                               ; preds = %66
  store i64 0, ptr %27, align 8
  br label %73

73:                                               ; preds = %151, %72
  %74 = load i64, ptr %27, align 8
  %75 = load i64, ptr %22, align 8
  %76 = sdiv i64 %75, 2
  %77 = icmp slt i64 %74, %76
  br i1 %77, label %78, label %154

78:                                               ; preds = %73
  %79 = load ptr, ptr %16, align 8
  %80 = load i64, ptr %26, align 8
  %81 = load i64, ptr %22, align 8
  %82 = mul nsw i64 %80, %81
  %83 = load i64, ptr %27, align 8
  %84 = add nsw i64 %82, %83
  %85 = getelementptr inbounds i64, ptr %79, i64 %84
  %86 = load i64, ptr %85, align 8
  store i64 %86, ptr %28, align 8
  %87 = load ptr, ptr %16, align 8
  %88 = load i64, ptr %26, align 8
  %89 = load i64, ptr %22, align 8
  %90 = mul nsw i64 %88, %89
  %91 = load i64, ptr %27, align 8
  %92 = add nsw i64 %90, %91
  %93 = load i64, ptr %22, align 8
  %94 = sdiv i64 %93, 2
  %95 = add nsw i64 %92, %94
  %96 = getelementptr inbounds i64, ptr %87, i64 %95
  %97 = load i64, ptr %96, align 8
  store i64 %97, ptr %29, align 8
  %98 = load ptr, ptr %19, align 8
  %99 = load i64, ptr %27, align 8
  %100 = mul nsw i64 2, %99
  %101 = add nsw i64 %100, 1
  %102 = load i64, ptr %24, align 8
  %103 = mul nsw i64 %101, %102
  %104 = getelementptr inbounds i64, ptr %98, i64 %103
  %105 = load i64, ptr %104, align 8
  store i64 %105, ptr %30, align 8
  %106 = load i64, ptr %28, align 8
  %107 = load i64, ptr %29, align 8
  %108 = load i64, ptr %30, align 8
  %109 = load i64, ptr %18, align 8
  store i64 %106, ptr %9, align 8
  store i64 %107, ptr %10, align 8
  store i64 %108, ptr %11, align 8
  store i64 %109, ptr %12, align 8
  store ptr %31, ptr %13, align 8
  store ptr %32, ptr %14, align 8
  %110 = load i64, ptr %9, align 8
  %111 = load i64, ptr %11, align 8
  %112 = load i64, ptr %10, align 8
  %113 = mul nsw i64 %111, %112
  %114 = load i64, ptr %12, align 8
  %115 = srem i64 %113, %114
  %116 = add nsw i64 %110, %115
  %117 = load i64, ptr %12, align 8
  %118 = srem i64 %116, %117
  %119 = load ptr, ptr %13, align 8
  store i64 %118, ptr %119, align 8
  %120 = load i64, ptr %9, align 8
  %121 = load i64, ptr %11, align 8
  %122 = load i64, ptr %10, align 8
  %123 = mul nsw i64 %121, %122
  %124 = load i64, ptr %12, align 8
  %125 = srem i64 %123, %124
  %126 = sub nsw i64 %120, %125
  %127 = load i64, ptr %12, align 8
  %128 = add nsw i64 %126, %127
  %129 = load i64, ptr %12, align 8
  %130 = srem i64 %128, %129
  %131 = load ptr, ptr %14, align 8
  store i64 %130, ptr %131, align 8
  %132 = load i64, ptr %31, align 8
  %133 = load ptr, ptr %16, align 8
  %134 = load i64, ptr %26, align 8
  %135 = load i64, ptr %22, align 8
  %136 = mul nsw i64 %134, %135
  %137 = load i64, ptr %27, align 8
  %138 = add nsw i64 %136, %137
  %139 = getelementptr inbounds i64, ptr %133, i64 %138
  store i64 %132, ptr %139, align 8
  %140 = load i64, ptr %32, align 8
  %141 = load ptr, ptr %16, align 8
  %142 = load i64, ptr %26, align 8
  %143 = load i64, ptr %22, align 8
  %144 = mul nsw i64 %142, %143
  %145 = load i64, ptr %27, align 8
  %146 = add nsw i64 %144, %145
  %147 = load i64, ptr %22, align 8
  %148 = sdiv i64 %147, 2
  %149 = add nsw i64 %146, %148
  %150 = getelementptr inbounds i64, ptr %141, i64 %149
  store i64 %140, ptr %150, align 8
  br label %151

151:                                              ; preds = %78
  %152 = load i64, ptr %27, align 8
  %153 = add nsw i64 %152, 1
  store i64 %153, ptr %27, align 8
  br label %73, !llvm.loop !8

154:                                              ; preds = %73
  br label %155

155:                                              ; preds = %154
  %156 = load i64, ptr %26, align 8
  %157 = add nsw i64 %156, 1
  store i64 %157, ptr %26, align 8
  br label %66, !llvm.loop !9

158:                                              ; preds = %66
  %159 = load i64, ptr %24, align 8
  %160 = sdiv i64 %159, 2
  store i64 %160, ptr %24, align 8
  %161 = load i64, ptr %20, align 8
  %162 = icmp ne i64 %161, 0
  br i1 %162, label %163, label %166

163:                                              ; preds = %158
  %164 = load i64, ptr %22, align 8
  %165 = sdiv i64 %164, 2
  br label %169

166:                                              ; preds = %158
  %167 = load i64, ptr %22, align 8
  %168 = mul nsw i64 %167, 2
  br label %169

169:                                              ; preds = %166, %163
  %170 = phi i64 [ %165, %163 ], [ %168, %166 ]
  store i64 %170, ptr %22, align 8
  %171 = load i64, ptr %20, align 8
  %172 = icmp ne i64 %171, 0
  br i1 %172, label %173, label %176

173:                                              ; preds = %169
  %174 = load i64, ptr %23, align 8
  %175 = mul nsw i64 %174, 2
  br label %179

176:                                              ; preds = %169
  %177 = load i64, ptr %23, align 8
  %178 = sdiv i64 %177, 2
  br label %179

179:                                              ; preds = %176, %173
  %180 = phi i64 [ %175, %173 ], [ %178, %176 ]
  store i64 %180, ptr %23, align 8
  br label %181

181:                                              ; preds = %179
  %182 = load i64, ptr %25, align 8
  %183 = add nsw i64 %182, 1
  store i64 %183, ptr %25, align 8
  br label %50, !llvm.loop !10

184:                                              ; preds = %62
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
