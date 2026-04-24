; ModuleID = 'fastntt.cpp'
source_filename = "fastntt.cpp"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%"struct.std::_Vector_base" = type { %"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl" }
%"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl" = type { %"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data" }
%"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data" = type { ptr, ptr, ptr }

$_ZNSt6vectorIiSaIiEEixEm = comdat any

$_ZNKSt6vectorIiSaIiEEixEm = comdat any

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define dso_local void @_Z6bflyCTiiiiRiS_(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef nonnull align 4 dereferenceable(4) %4, ptr noundef nonnull align 4 dereferenceable(4) %5) #0 {
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

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define dso_local void @_Z6bflyGSiiiiRiS_(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3, ptr noundef nonnull align 4 dereferenceable(4) %4, ptr noundef nonnull align 4 dereferenceable(4) %5) #0 {
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

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define dso_local void @_Z7fastNTTRSt6vectorIiSaIiEEiiRKS1_b(ptr noundef nonnull align 8 dereferenceable(24) %0, i32 noundef %1, i32 noundef %2, ptr noundef nonnull align 8 dereferenceable(24) %3, i1 noundef zeroext %4) #0 {
  %6 = alloca ptr, align 8
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca ptr, align 8
  %10 = alloca i8, align 1
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
  store ptr %0, ptr %6, align 8
  store i32 %1, ptr %7, align 4
  store i32 %2, ptr %8, align 4
  store ptr %3, ptr %9, align 8
  %22 = zext i1 %4 to i8
  store i8 %22, ptr %10, align 1
  %23 = load i8, ptr %10, align 1
  %24 = trunc i8 %23 to i1
  br i1 %24, label %25, label %27

25:                                               ; preds = %5
  %26 = load i32, ptr %7, align 4
  br label %28

27:                                               ; preds = %5
  br label %28

28:                                               ; preds = %27, %25
  %29 = phi i32 [ %26, %25 ], [ 2, %27 ]
  store i32 %29, ptr %11, align 4
  %30 = load i8, ptr %10, align 1
  %31 = trunc i8 %30 to i1
  br i1 %31, label %32, label %33

32:                                               ; preds = %28
  br label %36

33:                                               ; preds = %28
  %34 = load i32, ptr %7, align 4
  %35 = sdiv i32 %34, 2
  br label %36

36:                                               ; preds = %33, %32
  %37 = phi i32 [ 1, %32 ], [ %35, %33 ]
  store i32 %37, ptr %12, align 4
  %38 = load i32, ptr %7, align 4
  %39 = sdiv i32 %38, 2
  store i32 %39, ptr %13, align 4
  store i32 0, ptr %14, align 4
  br label %40

40:                                               ; preds = %144, %36
  %41 = load i32, ptr %14, align 4
  %42 = load i32, ptr %7, align 4
  %43 = call i32 @llvm.cttz.i32(i32 %42, i1 true)
  %44 = icmp slt i32 %41, %43
  br i1 %44, label %45, label %147

45:                                               ; preds = %40
  store i32 0, ptr %15, align 4
  br label %46

46:                                               ; preds = %118, %45
  %47 = load i32, ptr %15, align 4
  %48 = load i32, ptr %7, align 4
  %49 = load i32, ptr %11, align 4
  %50 = sdiv i32 %48, %49
  %51 = icmp slt i32 %47, %50
  br i1 %51, label %52, label %121

52:                                               ; preds = %46
  store i32 0, ptr %16, align 4
  br label %53

53:                                               ; preds = %114, %52
  %54 = load i32, ptr %16, align 4
  %55 = load i32, ptr %11, align 4
  %56 = sdiv i32 %55, 2
  %57 = icmp slt i32 %54, %56
  br i1 %57, label %58, label %117

58:                                               ; preds = %53
  %59 = load ptr, ptr %6, align 8
  %60 = load i32, ptr %15, align 4
  %61 = load i32, ptr %11, align 4
  %62 = mul nsw i32 %60, %61
  %63 = load i32, ptr %16, align 4
  %64 = add nsw i32 %62, %63
  %65 = sext i32 %64 to i64
  %66 = call noundef nonnull align 4 dereferenceable(4) ptr @_ZNSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %59, i64 noundef %65) #2
  %67 = load i32, ptr %66, align 4
  store i32 %67, ptr %17, align 4
  %68 = load ptr, ptr %6, align 8
  %69 = load i32, ptr %15, align 4
  %70 = load i32, ptr %11, align 4
  %71 = mul nsw i32 %69, %70
  %72 = load i32, ptr %16, align 4
  %73 = add nsw i32 %71, %72
  %74 = load i32, ptr %11, align 4
  %75 = sdiv i32 %74, 2
  %76 = add nsw i32 %73, %75
  %77 = sext i32 %76 to i64
  %78 = call noundef nonnull align 4 dereferenceable(4) ptr @_ZNSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %68, i64 noundef %77) #2
  %79 = load i32, ptr %78, align 4
  store i32 %79, ptr %18, align 4
  %80 = load ptr, ptr %9, align 8
  %81 = load i32, ptr %16, align 4
  %82 = mul nsw i32 2, %81
  %83 = add nsw i32 %82, 1
  %84 = load i32, ptr %13, align 4
  %85 = mul nsw i32 %83, %84
  %86 = sext i32 %85 to i64
  %87 = call noundef nonnull align 4 dereferenceable(4) ptr @_ZNKSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %80, i64 noundef %86) #2
  %88 = load i32, ptr %87, align 4
  store i32 %88, ptr %19, align 4
  %89 = load i32, ptr %17, align 4
  %90 = load i32, ptr %18, align 4
  %91 = load i32, ptr %19, align 4
  %92 = load i32, ptr %8, align 4
  call void @_Z6bflyCTiiiiRiS_(i32 noundef %89, i32 noundef %90, i32 noundef %91, i32 noundef %92, ptr noundef nonnull align 4 dereferenceable(4) %20, ptr noundef nonnull align 4 dereferenceable(4) %21)
  %93 = load i32, ptr %20, align 4
  %94 = load ptr, ptr %6, align 8
  %95 = load i32, ptr %15, align 4
  %96 = load i32, ptr %11, align 4
  %97 = mul nsw i32 %95, %96
  %98 = load i32, ptr %16, align 4
  %99 = add nsw i32 %97, %98
  %100 = sext i32 %99 to i64
  %101 = call noundef nonnull align 4 dereferenceable(4) ptr @_ZNSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %94, i64 noundef %100) #2
  store i32 %93, ptr %101, align 4
  %102 = load i32, ptr %21, align 4
  %103 = load ptr, ptr %6, align 8
  %104 = load i32, ptr %15, align 4
  %105 = load i32, ptr %11, align 4
  %106 = mul nsw i32 %104, %105
  %107 = load i32, ptr %16, align 4
  %108 = add nsw i32 %106, %107
  %109 = load i32, ptr %11, align 4
  %110 = sdiv i32 %109, 2
  %111 = add nsw i32 %108, %110
  %112 = sext i32 %111 to i64
  %113 = call noundef nonnull align 4 dereferenceable(4) ptr @_ZNSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %103, i64 noundef %112) #2
  store i32 %102, ptr %113, align 4
  br label %114

114:                                              ; preds = %58
  %115 = load i32, ptr %16, align 4
  %116 = add nsw i32 %115, 1
  store i32 %116, ptr %16, align 4
  br label %53, !llvm.loop !6

117:                                              ; preds = %53
  br label %118

118:                                              ; preds = %117
  %119 = load i32, ptr %15, align 4
  %120 = add nsw i32 %119, 1
  store i32 %120, ptr %15, align 4
  br label %46, !llvm.loop !8

121:                                              ; preds = %46
  %122 = load i32, ptr %13, align 4
  %123 = sdiv i32 %122, 2
  store i32 %123, ptr %13, align 4
  %124 = load i8, ptr %10, align 1
  %125 = trunc i8 %124 to i1
  br i1 %125, label %126, label %129

126:                                              ; preds = %121
  %127 = load i32, ptr %11, align 4
  %128 = sdiv i32 %127, 2
  br label %132

129:                                              ; preds = %121
  %130 = load i32, ptr %11, align 4
  %131 = mul nsw i32 %130, 2
  br label %132

132:                                              ; preds = %129, %126
  %133 = phi i32 [ %128, %126 ], [ %131, %129 ]
  store i32 %133, ptr %11, align 4
  %134 = load i8, ptr %10, align 1
  %135 = trunc i8 %134 to i1
  br i1 %135, label %136, label %139

136:                                              ; preds = %132
  %137 = load i32, ptr %12, align 4
  %138 = mul nsw i32 %137, 2
  br label %142

139:                                              ; preds = %132
  %140 = load i32, ptr %12, align 4
  %141 = sdiv i32 %140, 2
  br label %142

142:                                              ; preds = %139, %136
  %143 = phi i32 [ %138, %136 ], [ %141, %139 ]
  store i32 %143, ptr %12, align 4
  br label %144

144:                                              ; preds = %142
  %145 = load i32, ptr %14, align 4
  %146 = add nsw i32 %145, 1
  store i32 %146, ptr %14, align 4
  br label %40, !llvm.loop !9

147:                                              ; preds = %40
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.cttz.i32(i32, i1 immarg) #1

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define linkonce_odr dso_local noundef nonnull align 4 dereferenceable(4) ptr @_ZNSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %0, i64 noundef %1) #0 comdat align 2 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load ptr, ptr %3, align 8
  %6 = getelementptr inbounds %"struct.std::_Vector_base", ptr %5, i32 0, i32 0
  %7 = getelementptr inbounds %"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", ptr %6, i32 0, i32 0
  %8 = load ptr, ptr %7, align 8
  %9 = load i64, ptr %4, align 8
  %10 = getelementptr inbounds i32, ptr %8, i64 %9
  ret ptr %10
}

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define linkonce_odr dso_local noundef nonnull align 4 dereferenceable(4) ptr @_ZNKSt6vectorIiSaIiEEixEm(ptr noundef nonnull align 8 dereferenceable(24) %0, i64 noundef %1) #0 comdat align 2 {
  %3 = alloca ptr, align 8
  %4 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load ptr, ptr %3, align 8
  %6 = getelementptr inbounds %"struct.std::_Vector_base", ptr %5, i32 0, i32 0
  %7 = getelementptr inbounds %"struct.std::_Vector_base<int, std::allocator<int>>::_Vector_impl_data", ptr %6, i32 0, i32 0
  %8 = load ptr, ptr %7, align 8
  %9 = load i64, ptr %4, align 8
  %10 = getelementptr inbounds i32, ptr %8, i64 %9
  ret ptr %10
}

attributes #0 = { mustprogress noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { nounwind }

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
