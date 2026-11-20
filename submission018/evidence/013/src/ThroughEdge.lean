import FixedSWitness

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

private def throughRows : Rows :=
  [(.m7, (w! "yxYXYx", w! "xxxYYYY")),
   (.m9, (w! "xYXYxy", w! "xxxYYYY")),
   (.m5, (w! "xYXYxy", w! "xxxYYYYYXyxyX")),
   (.m11, (w! "xYXYxy", w! "xxYYYYYXyxy")),
   (.m5, (w! "xYXYxy", w! "xxYYYYYXyyxyX")),
   (.m11, (w! "xYXYxy", w! "xYYYYYXyyxy")),
   (.m3, (w! "xYXYYYxyyyyyX", w! "xYYYYYXyyxy")),
   (.m7, (w! "YXYYYxyyyyy", w! "xYYYYYXyyxy")),
   (.m0, (w! "YYYYYXyyyxy", w! "xYYYYYXyyxy")),
   (.m5, (w! "YYYYYXyyyxy", w! "xYYYYYXYxyyyyy")),
   (.m11, (w! "YYYYYXyyyxy", w! "YYYYYXYxyyyyyx")),
   (.m8, (w! "YYYYXyyyx", w! "YYYYYXYxyyyyyx")),
   (.m5, (w! "YYYYXyyyx", w! "YYYYYXYxyyxyyyy")),
   (.m12, (w! "YYYYXyyyx", w! "YYYYXYxyyxyyy")),
   (.m12, (w! "YYYYXyyyx", w! "YYYXYxyyxyy")),
   (.m12, (w! "YYYYXyyyx", w! "YYXYxyyxy")),
   (.m12, (w! "YYYYXyyyx", w! "YXYxyyx")),
   (.m5, (w! "YYYYXyyyx", w! "YXYxYxyyyy")),
   (.m12, (w! "YYYYXyyyx", w! "XYxYxyyy")),
   (.m4, (w! "YYYYXyyyx", w! "XYxYxYXyyyx")),
   (.m10, (w! "YYYYXyyyx", w! "YxYxYXyyy")),
   (.m12, (w! "YYYYXyyyx", w! "xYxYXyy")),
   (.m11, (w! "YYYYXyyyx", w! "YxYXyyx")),
   (.m5, (w! "YYYYXyyyx", w! "YxYXYxyyyy")),
   (.m12, (w! "YYYYXyyyx", w! "xYXYxyyy")),
   (.m11, (w! "YYYYXyyyx", w! "YXYxyyyx")),
   (.m5, (w! "YYYYXyyyx", w! "YXYxxyyyy")),
   (.m12, (w! "YYYYXyyyx", w! "XYxxyyy")),
   (.m4, (w! "YYYYXyyyx", w! "XYxxYXyyyx")),
   (.m10, (w! "YYYYXyyyx", w! "YxxYXyyy")),
   (.m12, (w! "YYYYXyyyx", w! "xxYXyy")),
   (.m12, (w! "YYYYXyyyx", w! "yxxYXy")),
   (.m12, (w! "YYYYXyyyx", w! "yyxxYX")),
   (.m6, (w! "xYYYYXyyy", w! "yyxxYX")),
   (.m4, (w! "xYYYYXyyy", w! "yyxxYYYYYXyyy")),
   (.m13, (w! "xYYYYXyyy", w! "yxxYYYYYXyyyy")),
   (.m13, (w! "xYYYYXyyy", w! "xxYYYYYXyyyyy")),
   (.m8, (w! "yxYYYYXyy", w! "xxYYYYYXyyyyy")),
   (.m8, (w! "yyxYYYYXy", w! "xxYYYYYXyyyyy")),
   (.m8, (w! "yyyxYYYYX", w! "xxYYYYYXyyyyy")),
   (.m7, (w! "XyyyxYYYY", w! "xxYYYYYXyyyyy"))]

def through25 := throughRows.map Prod.fst

theorem through25_ok : through25.length = 41 ∧ Witness 25 ak3 source through25 ∧
    peak through25 ak3 = 25 ∧ avoids through25 ak3 = false := by
  obtain ⟨he,hp,ha⟩ := trace_sound (s := ak3) (rs := throughRows) (by decide +kernel)
  exact ⟨by decide +kernel, ⟨he.trans (by decide +kernel),hp.le.trans (by decide +kernel)⟩,
    hp.trans (by decide +kernel),ha.trans (by decide +kernel)⟩

theorem through25_move35 : (through25.take 34).length = 34 ∧
    wordRun (through25.take 34) ak3 = U ∧ through25[34]? = some .m4 ∧ wordStep .m4 U = V := by
  have ok : traceOK ak3 (throughRows.take 34) = true := by decide +kernel
  have hd := (trace_sound ok).1
  rw [List.map_take] at hd
  exact ⟨by decide +kernel,hd.trans (by decide +kernel),by decide +kernel,by decide +kernel⟩

end Candidate.AK3Peak.FixedS
