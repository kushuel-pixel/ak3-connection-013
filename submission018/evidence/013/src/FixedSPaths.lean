import FixedSWitness

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

private def bypass22Rows : Rows :=
  [(.m12, (w! "xyxYXY", w! "yxxxYYYYY")),
   (.m10, (w! "xyxYXY", w! "xyxxxYYYYYX")),
   (.m1, (w! "xyxYXY", w! "xyyyyyXXXYX")),
   (.m4, (w! "xyxYXY", w! "xyyyyyXXYXY")),
   (.m13, (w! "xyxYXY", w! "YxyyyyyXXYX")),
   (.m4, (w! "xyxYXY", w! "YxyyyyyXYXY")),
   (.m13, (w! "xyxYXY", w! "YYxyyyyyXYX")),
   (.m0, (w! "yxyXYX", w! "YYxyyyyyXYX")),
   (.m3, (w! "yxYYYYXyy", w! "YYxyyyyyXYX")),
   (.m11, (w! "yxYYYYXyy", w! "XYYxyyyyyXY")),
   (.m4, (w! "yxYYYYXyy", w! "XYYxyXyy")),
   (.m9, (w! "xYYYYXyyy", w! "XYYxyXyy")),
   (.m7, (w! "YYYYXyyyx", w! "XYYxyXyy")),
   (.m1, (w! "YYYYXyyyx", w! "YYxYXyyx")),
   (.m5, (w! "YYYYXyyyx", w! "YYxYXYxyyyy")),
   (.m12, (w! "YYYYXyyyx", w! "YxYXYxyyy")),
   (.m0, (w! "XYYYxyyyy", w! "YxYXYxyyy")),
   (.m6, (w! "YYYxyyyyX", w! "YxYXYxyyy")),
   (.m12, (w! "YYYxyyyyX", w! "xYXYxyy")),
   (.m4, (w! "YYYxyyyyX", w! "xYXYxYxyyyyX")),
   (.m11, (w! "YYYxyyyyX", w! "YXYxYxyyyy")),
   (.m12, (w! "YYYxyyyyX", w! "XYxYxyyy")),
   (.m10, (w! "YYYxyyyyX", w! "YxYxyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "YxYxYXyyy")),
   (.m12, (w! "YYYxyyyyX", w! "xYxYXyy")),
   (.m4, (w! "YYYxyyyyX", w! "xYxYXYxyyyyX")),
   (.m11, (w! "YYYxyyyyX", w! "YxYXYxyyyy")),
   (.m12, (w! "YYYxyyyyX", w! "xYXYxyyy")),
   (.m4, (w! "YYYxyyyyX", w! "xYXYxxyyyyX")),
   (.m11, (w! "YYYxyyyyX", w! "YXYxxyyyy")),
   (.m12, (w! "YYYxyyyyX", w! "XYxxyyy")),
   (.m10, (w! "YYYxyyyyX", w! "YxxyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "YxxYXyyy")),
   (.m12, (w! "YYYxyyyyX", w! "xxYXyy")),
   (.m12, (w! "YYYxyyyyX", w! "yxxYXy")),
   (.m12, (w! "YYYxyyyyX", w! "yyxxYX")),
   (.m5, (w! "YYYxyyyyX", w! "yyxxYYYYYXyyy")),
   (.m0, (w! "xYYYYXyyy", w! "yyxxYYYYYXyyy")),
   (.m8, (w! "yxYYYYXyy", w! "yyxxYYYYYXyyy")),
   (.m8, (w! "yyxYYYYXy", w! "yyxxYYYYYXyyy")),
   (.m8, (w! "yyyxYYYYX", w! "yyxxYYYYYXyyy")),
   (.m7, (w! "XyyyxYYYY", w! "yyxxYYYYYXyyy")),
   (.m13, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m13, (w! "XyyyxYYYY", w! "xxYYYYYXyyyyy"))]

def bypass22 : List Move := bypass22Rows.map Prod.fst

theorem bypass22_ok : bypass22.length = 44 ∧ peak bypass22 ak3 = 22 ∧
    AvoidWitness 22 ak3 source bypass22 :=
  certified bypass22Rows (by decide +kernel)

private def back22Rows : Rows :=
  [(.m12, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m12, (w! "XyyyxYYYY", w! "yyxxYYYYYXyyy")),
   (.m6, (w! "yyyxYYYYX", w! "yyxxYYYYYXyyy")),
   (.m9, (w! "yyxYYYYXy", w! "yyxxYYYYYXyyy")),
   (.m9, (w! "yxYYYYXyy", w! "yyxxYYYYYXyyy")),
   (.m9, (w! "xYYYYXyyy", w! "yyxxYYYYYXyyy")),
   (.m0, (w! "YYYxyyyyX", w! "yyxxYYYYYXyyy")),
   (.m4, (w! "YYYxyyyyX", w! "yyxxYX")),
   (.m13, (w! "YYYxyyyyX", w! "yxxYXy")),
   (.m13, (w! "YYYxyyyyX", w! "xxYXyy")),
   (.m13, (w! "YYYxyyyyX", w! "YxxYXyyy")),
   (.m4, (w! "YYYxyyyyX", w! "YxxyyyX")),
   (.m11, (w! "YYYxyyyyX", w! "XYxxyyy")),
   (.m13, (w! "YYYxyyyyX", w! "YXYxxyyyy")),
   (.m10, (w! "YYYxyyyyX", w! "xYXYxxyyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "xYXYxyyy")),
   (.m13, (w! "YYYxyyyyX", w! "YxYXYxyyyy")),
   (.m10, (w! "YYYxyyyyX", w! "xYxYXYxyyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "xYxYXyy")),
   (.m13, (w! "YYYxyyyyX", w! "YxYxYXyyy")),
   (.m4, (w! "YYYxyyyyX", w! "YxYxyyyX")),
   (.m11, (w! "YYYxyyyyX", w! "XYxYxyyy")),
   (.m13, (w! "YYYxyyyyX", w! "YXYxYxyyyy")),
   (.m10, (w! "YYYxyyyyX", w! "xYXYxYxyyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "xYXYxyy")),
   (.m13, (w! "YYYxyyyyX", w! "YxYXYxyyy")),
   (.m7, (w! "XYYYxyyyy", w! "YxYXYxyyy")),
   (.m0, (w! "YYYYXyyyx", w! "YxYXYxyyy")),
   (.m13, (w! "YYYYXyyyx", w! "YYxYXYxyyyy")),
   (.m4, (w! "YYYYXyyyx", w! "YYxYXyyx")),
   (.m1, (w! "YYYYXyyyx", w! "XYYxyXyy")),
   (.m6, (w! "xYYYYXyyy", w! "XYYxyXyy")),
   (.m8, (w! "yxYYYYXyy", w! "XYYxyXyy")),
   (.m5, (w! "yxYYYYXyy", w! "XYYxyyyyyXY")),
   (.m10, (w! "yxYYYYXyy", w! "YYxyyyyyXYX")),
   (.m2, (w! "yxyXYX", w! "YYxyyyyyXYX")),
   (.m0, (w! "xyxYXY", w! "YYxyyyyyXYX")),
   (.m12, (w! "xyxYXY", w! "YxyyyyyXYXY")),
   (.m5, (w! "xyxYXY", w! "YxyyyyyXXYX")),
   (.m12, (w! "xyxYXY", w! "xyyyyyXXYXY")),
   (.m5, (w! "xyxYXY", w! "xyyyyyXXXYX")),
   (.m1, (w! "xyxYXY", w! "xyxxxYYYYYX")),
   (.m11, (w! "xyxYXY", w! "yxxxYYYYY")),
   (.m13, (w! "xyxYXY", w! "xxxYYYY"))]

def back22 : List Move := back22Rows.map Prod.fst

theorem back22_ok : back22.length = 44 ∧ peak back22 source = 22 ∧
    AvoidWitness 22 source ak3 back22 :=
  certified back22Rows (by decide +kernel)

theorem back22_inverse : back22 = reverseMoves bypass22 := by decide +kernel

private def bypass23Rows : Rows :=
  [(.m12, (w! "xyxYXY", w! "yxxxYYYYY")),
   (.m10, (w! "xyxYXY", w! "xyxxxYYYYYX")),
   (.m1, (w! "xyxYXY", w! "xyyyyyXXXYX")),
   (.m4, (w! "xyxYXY", w! "xyyyyyXXYXY")),
   (.m8, (w! "yxyxYXYY", w! "xyyyyyXXYXY")),
   (.m4, (w! "yxyxYXYY", w! "xyyyyyXYXYY")),
   (.m8, (w! "yyxyxYXYYY", w! "xyyyyyXYXYY")),
   (.m0, (w! "yyyxyXYXYY", w! "xyyyyyXYXYY")),
   (.m3, (w! "yyyxYYYYX", w! "xyyyyyXYXYY")),
   (.m12, (w! "yyyxYYYYX", w! "yxyyyyyXYXYYY")),
   (.m4, (w! "yyyxYYYYX", w! "yxyyyyyXYYYYYX")),
   (.m11, (w! "yyyxYYYYX", w! "XyxyyyyyXYYYYY")),
   (.m13, (w! "yyyxYYYYX", w! "YXyxyyyyyXYYYY")),
   (.m13, (w! "yyyxYYYYX", w! "YYXyxyyyyyXYYY")),
   (.m4, (w! "yyyxYYYYX", w! "YYXyxyX")),
   (.m12, (w! "yyyxYYYYX", w! "YXyxyXY")),
   (.m12, (w! "yyyxYYYYX", w! "XyxyXYY")),
   (.m12, (w! "yyyxYYYYX", w! "yXyxyXYYY")),
   (.m4, (w! "yyyxYYYYX", w! "yXyxYYYX")),
   (.m11, (w! "yyyxYYYYX", w! "XyXyxYYY")),
   (.m12, (w! "yyyxYYYYX", w! "yXyXyxYYYY")),
   (.m10, (w! "yyyxYYYYX", w! "xyXyXyxYYYYX")),
   (.m5, (w! "yyyxYYYYX", w! "xyXyXYY")),
   (.m12, (w! "yyyxYYYYX", w! "yxyXyXYYY")),
   (.m4, (w! "yyyxYYYYX", w! "yxyXYYYX")),
   (.m6, (w! "xyyyxYYYYXX", w! "yxyXYYYX")),
   (.m4, (w! "xyyyxYYYYXX", w! "yxYYYXX")),
   (.m1, (w! "xyyyxYYYYXX", w! "xxyyyXY")),
   (.m7, (w! "yyyxYYYYX", w! "xxyyyXY")),
   (.m9, (w! "yyxYYYYXy", w! "xxyyyXY")),
   (.m9, (w! "yxYYYYXyy", w! "xxyyyXY")),
   (.m4, (w! "yxYYYYXyy", w! "xxYXyy")),
   (.m12, (w! "yxYYYYXyy", w! "yxxYXy")),
   (.m12, (w! "yxYYYYXyy", w! "yyxxYX")),
   (.m12, (w! "yxYYYYXyy", w! "yyyxxYXY")),
   (.m4, (w! "yxYYYYXyy", w! "yyyxxYYYYYXyy")),
   (.m8, (w! "yyxYYYYXy", w! "yyyxxYYYYYXyy")),
   (.m8, (w! "yyyxYYYYX", w! "yyyxxYYYYYXyy")),
   (.m7, (w! "XyyyxYYYY", w! "yyyxxYYYYYXyy")),
   (.m13, (w! "XyyyxYYYY", w! "yyxxYYYYYXyyy")),
   (.m13, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m13, (w! "XyyyxYYYY", w! "xxYYYYYXyyyyy"))]

def bypass23 : List Move := bypass23Rows.map Prod.fst

theorem bypass23_ok : bypass23.length = 42 ∧ peak bypass23 ak3 = 23 ∧
    AvoidWitness 23 ak3 source bypass23 :=
  certified bypass23Rows (by decide +kernel)

private def back23Rows : Rows :=
  [(.m12, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m12, (w! "XyyyxYYYY", w! "yyxxYYYYYXyyy")),
   (.m12, (w! "XyyyxYYYY", w! "yyyxxYYYYYXyy")),
   (.m6, (w! "yyyxYYYYX", w! "yyyxxYYYYYXyy")),
   (.m9, (w! "yyxYYYYXy", w! "yyyxxYYYYYXyy")),
   (.m9, (w! "yxYYYYXyy", w! "yyyxxYYYYYXyy")),
   (.m5, (w! "yxYYYYXyy", w! "yyyxxYXY")),
   (.m13, (w! "yxYYYYXyy", w! "yyxxYX")),
   (.m13, (w! "yxYYYYXyy", w! "yxxYXy")),
   (.m13, (w! "yxYYYYXyy", w! "xxYXyy")),
   (.m5, (w! "yxYYYYXyy", w! "xxyyyXY")),
   (.m8, (w! "yyxYYYYXy", w! "xxyyyXY")),
   (.m8, (w! "yyyxYYYYX", w! "xxyyyXY")),
   (.m6, (w! "xyyyxYYYYXX", w! "xxyyyXY")),
   (.m1, (w! "xyyyxYYYYXX", w! "yxYYYXX")),
   (.m5, (w! "xyyyxYYYYXX", w! "yxyXYYYX")),
   (.m7, (w! "yyyxYYYYX", w! "yxyXYYYX")),
   (.m5, (w! "yyyxYYYYX", w! "yxyXyXYYY")),
   (.m13, (w! "yyyxYYYYX", w! "xyXyXYY")),
   (.m4, (w! "yyyxYYYYX", w! "xyXyXyxYYYYX")),
   (.m11, (w! "yyyxYYYYX", w! "yXyXyxYYYY")),
   (.m13, (w! "yyyxYYYYX", w! "XyXyxYYY")),
   (.m10, (w! "yyyxYYYYX", w! "yXyxYYYX")),
   (.m5, (w! "yyyxYYYYX", w! "yXyxyXYYY")),
   (.m13, (w! "yyyxYYYYX", w! "XyxyXYY")),
   (.m13, (w! "yyyxYYYYX", w! "YXyxyXY")),
   (.m13, (w! "yyyxYYYYX", w! "YYXyxyX")),
   (.m5, (w! "yyyxYYYYX", w! "YYXyxyyyyyXYYY")),
   (.m12, (w! "yyyxYYYYX", w! "YXyxyyyyyXYYYY")),
   (.m12, (w! "yyyxYYYYX", w! "XyxyyyyyXYYYYY")),
   (.m10, (w! "yyyxYYYYX", w! "yxyyyyyXYYYYYX")),
   (.m5, (w! "yyyxYYYYX", w! "yxyyyyyXYXYYY")),
   (.m13, (w! "yyyxYYYYX", w! "xyyyyyXYXYY")),
   (.m2, (w! "yyyxyXYXYY", w! "xyyyyyXYXYY")),
   (.m0, (w! "yyxyxYXYYY", w! "xyyyyyXYXYY")),
   (.m9, (w! "yxyxYXYY", w! "xyyyyyXYXYY")),
   (.m5, (w! "yxyxYXYY", w! "xyyyyyXXYXY")),
   (.m9, (w! "xyxYXY", w! "xyyyyyXXYXY")),
   (.m5, (w! "xyxYXY", w! "xyyyyyXXXYX")),
   (.m1, (w! "xyxYXY", w! "xyxxxYYYYYX")),
   (.m11, (w! "xyxYXY", w! "yxxxYYYYY")),
   (.m13, (w! "xyxYXY", w! "xxxYYYY"))]

def back23 : List Move := back23Rows.map Prod.fst

theorem back23_ok : back23.length = 42 ∧ peak back23 source = 23 ∧
    AvoidWitness 23 source ak3 back23 :=
  certified back23Rows (by decide +kernel)

theorem back23_inverse : back23 = reverseMoves bypass23 := by decide +kernel

private def bypass25Rows : Rows :=
  [(.m7, (w! "yxYXYx", w! "xxxYYYY")),
   (.m9, (w! "xYXYxy", w! "xxxYYYY")),
   (.m5, (w! "xYXYxy", w! "xxxYYYYYXyxyX")),
   (.m11, (w! "xYXYxy", w! "xxYYYYYXyxy")),
   (.m5, (w! "xYXYxy", w! "xxYYYYYXyyxyX")),
   (.m11, (w! "xYXYxy", w! "xYYYYYXyyxy")),
   (.m3, (w! "xYXYYYxyyyyyX", w! "xYYYYYXyyxy")),
   (.m7, (w! "YXYYYxyyyyy", w! "xYYYYYXyyxy")),
   (.m4, (w! "YXYYYxyyyyy", w! "xYYYYYXYxyyyyy")),
   (.m8, (w! "XYYYxyyyy", w! "xYYYYYXYxyyyyy")),
   (.m11, (w! "XYYYxyyyy", w! "YYYYYXYxyyyyyx")),
   (.m4, (w! "XYYYxyyyy", w! "YYYYYXYxyyxyyyy")),
   (.m12, (w! "XYYYxyyyy", w! "YYYYXYxyyxyyy")),
   (.m12, (w! "XYYYxyyyy", w! "YYYXYxyyxyy")),
   (.m12, (w! "XYYYxyyyy", w! "YYXYxyyxy")),
   (.m12, (w! "XYYYxyyyy", w! "YXYxyyx")),
   (.m4, (w! "XYYYxyyyy", w! "YXYxYxyyyy")),
   (.m0, (w! "YYYYXyyyx", w! "YXYxYxyyyy")),
   (.m6, (w! "xYYYYXyyy", w! "YXYxYxyyyy")),
   (.m12, (w! "xYYYYXyyy", w! "XYxYxyyy")),
   (.m10, (w! "xYYYYXyyy", w! "YxYxyyyX")),
   (.m4, (w! "xYYYYXyyy", w! "YxYxYXyyy")),
   (.m12, (w! "xYYYYXyyy", w! "xYxYXyy")),
   (.m5, (w! "xYYYYXyyy", w! "xYxYXYxyyyyX")),
   (.m11, (w! "xYYYYXyyy", w! "YxYXYxyyyy")),
   (.m12, (w! "xYYYYXyyy", w! "xYXYxyyy")),
   (.m5, (w! "xYYYYXyyy", w! "xYXYxxyyyyX")),
   (.m11, (w! "xYYYYXyyy", w! "YXYxxyyyy")),
   (.m12, (w! "xYYYYXyyy", w! "XYxxyyy")),
   (.m10, (w! "xYYYYXyyy", w! "YxxyyyX")),
   (.m4, (w! "xYYYYXyyy", w! "YxxYXyyy")),
   (.m9, (w! "YxYYYYXyyyy", w! "YxxYXyyy")),
   (.m12, (w! "YxYYYYXyyyy", w! "xxYXyy")),
   (.m12, (w! "YxYYYYXyyyy", w! "yxxYXy")),
   (.m4, (w! "YxYYYYXyyyy", w! "yxxYYYYYXyyyy")),
   (.m8, (w! "xYYYYXyyy", w! "yxxYYYYYXyyyy")),
   (.m8, (w! "yxYYYYXyy", w! "yxxYYYYYXyyyy")),
   (.m8, (w! "yyxYYYYXy", w! "yxxYYYYYXyyyy")),
   (.m8, (w! "yyyxYYYYX", w! "yxxYYYYYXyyyy")),
   (.m7, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m13, (w! "XyyyxYYYY", w! "xxYYYYYXyyyyy"))]

def bypass25 : List Move := bypass25Rows.map Prod.fst

theorem bypass25_ok : bypass25.length = 41 ∧ peak bypass25 ak3 = 25 ∧
    AvoidWitness 25 ak3 source bypass25 :=
  certified bypass25Rows (by decide +kernel)

private def back25Rows : Rows :=
  [(.m12, (w! "XyyyxYYYY", w! "yxxYYYYYXyyyy")),
   (.m6, (w! "yyyxYYYYX", w! "yxxYYYYYXyyyy")),
   (.m9, (w! "yyxYYYYXy", w! "yxxYYYYYXyyyy")),
   (.m9, (w! "yxYYYYXyy", w! "yxxYYYYYXyyyy")),
   (.m9, (w! "xYYYYXyyy", w! "yxxYYYYYXyyyy")),
   (.m9, (w! "YxYYYYXyyyy", w! "yxxYYYYYXyyyy")),
   (.m5, (w! "YxYYYYXyyyy", w! "yxxYXy")),
   (.m13, (w! "YxYYYYXyyyy", w! "xxYXyy")),
   (.m13, (w! "YxYYYYXyyyy", w! "YxxYXyyy")),
   (.m8, (w! "xYYYYXyyy", w! "YxxYXyyy")),
   (.m5, (w! "xYYYYXyyy", w! "YxxyyyX")),
   (.m11, (w! "xYYYYXyyy", w! "XYxxyyy")),
   (.m13, (w! "xYYYYXyyy", w! "YXYxxyyyy")),
   (.m10, (w! "xYYYYXyyy", w! "xYXYxxyyyyX")),
   (.m4, (w! "xYYYYXyyy", w! "xYXYxyyy")),
   (.m13, (w! "xYYYYXyyy", w! "YxYXYxyyyy")),
   (.m10, (w! "xYYYYXyyy", w! "xYxYXYxyyyyX")),
   (.m4, (w! "xYYYYXyyy", w! "xYxYXyy")),
   (.m13, (w! "xYYYYXyyy", w! "YxYxYXyyy")),
   (.m5, (w! "xYYYYXyyy", w! "YxYxyyyX")),
   (.m11, (w! "xYYYYXyyy", w! "XYxYxyyy")),
   (.m13, (w! "xYYYYXyyy", w! "YXYxYxyyyy")),
   (.m7, (w! "YYYYXyyyx", w! "YXYxYxyyyy")),
   (.m0, (w! "XYYYxyyyy", w! "YXYxYxyyyy")),
   (.m5, (w! "XYYYxyyyy", w! "YXYxyyx")),
   (.m13, (w! "XYYYxyyyy", w! "YYXYxyyxy")),
   (.m13, (w! "XYYYxyyyy", w! "YYYXYxyyxyy")),
   (.m13, (w! "XYYYxyyyy", w! "YYYYXYxyyxyyy")),
   (.m13, (w! "XYYYxyyyy", w! "YYYYYXYxyyxyyyy")),
   (.m5, (w! "XYYYxyyyy", w! "YYYYYXYxyyyyyx")),
   (.m10, (w! "XYYYxyyyy", w! "xYYYYYXYxyyyyy")),
   (.m9, (w! "YXYYYxyyyyy", w! "xYYYYYXYxyyyyy")),
   (.m5, (w! "YXYYYxyyyyy", w! "xYYYYYXyyxy")),
   (.m6, (w! "xYXYYYxyyyyyX", w! "xYYYYYXyyxy")),
   (.m2, (w! "xYXYxy", w! "xYYYYYXyyxy")),
   (.m10, (w! "xYXYxy", w! "xxYYYYYXyyxyX")),
   (.m4, (w! "xYXYxy", w! "xxYYYYYXyxy")),
   (.m10, (w! "xYXYxy", w! "xxxYYYYYXyxyX")),
   (.m4, (w! "xYXYxy", w! "xxxYYYY")),
   (.m8, (w! "yxYXYx", w! "xxxYYYY")),
   (.m6, (w! "xyxYXY", w! "xxxYYYY"))]

def back25 : List Move := back25Rows.map Prod.fst

theorem back25_ok : back25.length = 41 ∧ peak back25 source = 25 ∧
    AvoidWitness 25 source ak3 back25 :=
  certified back25Rows (by decide +kernel)

theorem back25_inverse : back25 = reverseMoves bypass25 := by decide +kernel

def lowP : WordState := (w! "xyXyxyXYYYYYYX", w! "XYXYYxy")
def lowQ : WordState := (w! "xyXyxyXYYYYYYX", w! "YXyyxyx")

private def approachRows : Rows :=
  [(.m6, (w! "yyyxYYYYX", w! "xxYYYYYXyyyyy")),
   (.m9, (w! "yyxYYYYXy", w! "xxYYYYYXyyyyy")),
   (.m9, (w! "yxYYYYXyy", w! "xxYYYYYXyyyyy")),
   (.m9, (w! "xYYYYXyyy", w! "xxYYYYYXyyyyy")),
   (.m7, (w! "YYYYXyyyx", w! "xxYYYYYXyyyyy")),
   (.m11, (w! "YYYYXyyyx", w! "xYYYYYXyyyyyx")),
   (.m11, (w! "YYYYXyyyx", w! "YYYYYXyyyyyxx")),
   (.m7, (w! "XYYYYXyyyxx", w! "YYYYYXyyyyyxx")),
   (.m5, (w! "XYYYYXyyyxx", w! "YYYYYXyyxyyyyx")),
   (.m6, (w! "YYYYXyyyx", w! "YYYYYXyyxyyyyx")),
   (.m10, (w! "YYYYXyyyx", w! "xYYYYYXyyxyyyy")),
   (.m1, (w! "YYYYXyyyx", w! "YYYYXYYxyyyyyX")),
   (.m10, (w! "YYYYXyyyx", w! "xYYYYXYYxyyyyyXX")),
   (.m6, (w! "xYYYYXyyy", w! "xYYYYXYYxyyyyyXX")),
   (.m0, (w! "YYYxyyyyX", w! "xYYYYXYYxyyyyyXX")),
   (.m11, (w! "YYYxyyyyX", w! "YYYYXYYxyyyyyX")),
   (.m5, (w! "YYYxyyyyX", w! "YYYYXYYxyXyyy")),
   (.m0, (w! "xYYYYXyyy", w! "YYYYXYYxyXyyy")),
   (.m7, (w! "YYYYXyyyx", w! "YYYYXYYxyXyyy")),
   (.m12, (w! "YYYYXyyyx", w! "YYYXYYxyXyy")),
   (.m12, (w! "YYYYXyyyx", w! "YYXYYxyXy")),
   (.m12, (w! "YYYYXyyyx", w! "YXYYxyX")),
   (.m12, (w! "YYYYXyyyx", w! "XYYxyXY")),
   (.m2, (w! "YYYYXyxyXY", w! "XYYxyXY")),
   (.m9, (w! "YYYYYXyxyX", w! "XYYxyXY")),
   (.m13, (w! "YYYYYXyxyX", w! "YXYYxyX")),
   (.m11, (w! "YYYYYXyxyX", w! "XYXYYxy")),
   (.m7, (w! "XYYYYYXyxy", w! "XYXYYxy")),
   (.m8, (w! "yXYYYYYXyx", w! "XYXYYxy")),
   (.m6, (w! "xyXYYYYYXy", w! "XYXYYxy")),
   (.m8, (w! "yxyXYYYYYX", w! "XYXYYxy")),
   (.m7, (w! "XyxyXYYYYY", w! "XYXYYxy")),
   (.m8, (w! "yXyxyXYYYYYY", w! "XYXYYxy")),
   (.m6, (w! "xyXyxyXYYYYYYX", w! "XYXYYxy"))]
def approach := approachRows.map Prod.fst
theorem approach_ok : Witness 27 source lowP approach := by
  obtain ⟨he,hp,_⟩ := trace_sound (s := source) (rs := approachRows) (by decide +kernel)
  exact ⟨he.trans (by decide +kernel), hp.le.trans (by decide +kernel)⟩

end Candidate.AK3Peak.FixedS
