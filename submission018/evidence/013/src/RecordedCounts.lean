import PathCount

namespace Candidate.AK3Peak.FixedS
open Verify.AtomicSemantics

private def layer0 : List WordState :=
  [(w! "xyxYXY", w! "xxxYYYY")]

private def layer1 : List WordState :=
  [(w! "yxYXYx", w! "xxxYYYY")]

private def layer2 : List WordState :=
  [(w! "xYXYxy", w! "xxxYYYY")]

private def layer3 : List WordState :=
  [(w! "xYXYxy", w! "xxxYYYYYXyxyX"),
   (w! "xYXYxyyyyyXXX", w! "xxxYYYY")]

private def layer4 : List WordState :=
  [(w! "xYXYxy", w! "xxYYYYYXyxy"),
   (w! "YXYxyyyyyXX", w! "xxxYYYY")]

private def layer5 : List WordState :=
  [(w! "xYXYxy", w! "xxYYYYYXyyxyX"),
   (w! "xYXYYxyyyyyXX", w! "xxYYYYYXyxy"),
   (w! "YXYxyyyyyXX", w! "xxxYYYYYXYxyyyyyXX")]

private def layer6 : List WordState :=
  [(w! "xYXYxy", w! "xYYYYYXyyxy"),
   (w! "YXYYxyyyyyX", w! "xxYYYYYXyxy"),
   (w! "YXYxyyyyyXX", w! "xxYYYYYXYxyyyyyX")]

private def layer7 : List WordState :=
  [(w! "xYXYYYxyyyyyX", w! "xYYYYYXyyxy"),
   (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX")]

private def layer8 : List WordState :=
  [(w! "YXYYYxyyyyy", w! "xYYYYYXyyxy"),
   (w! "xYYYYYXyyyxyX", w! "xYYYYYXyyxy"),
   (w! "YXYYxyyyyyX", w! "xYYYYYXYxyyyyy")]

private def layer9 : List WordState :=
  [(w! "YYYYYXyyyxy", w! "xYYYYYXyyxy"),
   (w! "YXYYYxyyyyy", w! "xYYYYYXYxyyyyy")]

private def layer10 : List WordState :=
  [(w! "XYYYxyyyy", w! "xYYYYYXYxyyyyy"),
   (w! "YXYYYxyyyyy", w! "YYYYYXYxyyyyyx"),
   (w! "YYYYYXyyyxy", w! "xYYYYYXYxyyyyy")]

private def layer11 : List WordState :=
  [(w! "XYYYxyyyy", w! "YYYYYXYxyyyyyx"),
   (w! "YYYYXyyyx", w! "xYYYYYXYxyyyyy"),
   (w! "YYYYYXyyyxy", w! "YYYYYXYxyyyyyx")]

private def layer12 : List WordState :=
  [(w! "YYYYXyyyx", w! "YYYYYXYxyyyyyx"),
   (w! "XYYYxyyyy", w! "YYYYYXYxyyxyyyy")]

private def layer13 : List WordState :=
  [(w! "XYYYxyyyy", w! "YYYYXYxyyxyyy"),
   (w! "YYYYXyyyx", w! "YYYYYXYxyyxyyyy")]

private def layer14 : List WordState :=
  [(w! "XYYYxyyyy", w! "YYYXYxyyxyy"),
   (w! "YYYYXyyyx", w! "YYYYXYxyyxyyy")]

private def layer15 : List WordState :=
  [(w! "XYYYxyyyy", w! "YYXYxyyxy"),
   (w! "YYYYXyyyx", w! "YYYXYxyyxyy")]

private def layer16 : List WordState :=
  [(w! "XYYYxyyyy", w! "YXYxyyx"),
   (w! "YYYYXyyyx", w! "YYXYxyyxy")]

private def layer17 : List WordState :=
  [(w! "YYYYXyyyx", w! "YXYxyyx"),
   (w! "XYYYxyyyy", w! "YXYxYxyyyy")]

private def layer18 : List WordState :=
  [(w! "XYYYxyyyy", w! "XYxYxyyy"),
   (w! "YYYxyyyyX", w! "YXYxYxyyyy"),
   (w! "YYYYXyyyx", w! "YXYxYxyyyy")]

private def layer19 : List WordState :=
  [(w! "XYYYxyyyy", w! "YxYxyyyX"),
   (w! "YYYxyyyyX", w! "XYxYxyyy"),
   (w! "YYYYXyyyx", w! "XYxYxyyy"),
   (w! "xYYYYXyyy", w! "YXYxYxyyyy"),
   (w! "XYYYxyyyy", w! "XYxYxYXyyyx")]

private def layer20 : List WordState :=
  [(w! "xYYYYXyyy", w! "XYxYxyyy"),
   (w! "YYYxyyyyX", w! "YxYxyyyX"),
   (w! "YYYYXyyyx", w! "YxYxyyyX"),
   (w! "XYYYxyyyy", w! "YxYxYXyyy"),
   (w! "YYYxyyyyX", w! "XYxYxYXyyyx"),
   (w! "YYYYXyyyx", w! "XYxYxYXyyyx")]

private def layer21 : List WordState :=
  [(w! "XYYYxyyyy", w! "xYxYXyy"),
   (w! "xYYYYXyyy", w! "YxYxyyyX"),
   (w! "YYYxyyyyX", w! "YxYxYXyyy"),
   (w! "YYYYXyyyx", w! "YxYxYXyyy"),
   (w! "xYYYYXyyy", w! "XYxYxYXyyyx")]

private def layer22 : List WordState :=
  [(w! "XYYYxyyyy", w! "YxYXyyx"),
   (w! "YYYxyyyyX", w! "xYxYXyy"),
   (w! "YYYYXyyyx", w! "xYxYXyy"),
   (w! "xYYYYXyyy", w! "YxYxYXyyy")]

private def layer23 : List WordState :=
  [(w! "xYYYYXyyy", w! "xYxYXyy"),
   (w! "YYYYXyyyx", w! "YxYXyyx"),
   (w! "XYYYxyyyy", w! "YxYXYxyyyy"),
   (w! "YYYxyyyyX", w! "xYxYXYxyyyyX")]

private def layer24 : List WordState :=
  [(w! "XYYYxyyyy", w! "xYXYxyyy"),
   (w! "YYYxyyyyX", w! "YxYXYxyyyy"),
   (w! "YYYYXyyyx", w! "YxYXYxyyyy"),
   (w! "xYYYYXyyy", w! "xYxYXYxyyyyX")]

private def layer25 : List WordState :=
  [(w! "XYYYxyyyy", w! "YXYxyyyx"),
   (w! "YYYxyyyyX", w! "xYXYxyyy"),
   (w! "YYYYXyyyx", w! "xYXYxyyy"),
   (w! "xYYYYXyyy", w! "YxYXYxyyyy")]

private def layer26 : List WordState :=
  [(w! "xYYYYXyyy", w! "xYXYxyyy"),
   (w! "YYYYXyyyx", w! "YXYxyyyx"),
   (w! "XYYYxyyyy", w! "YXYxxyyyy"),
   (w! "YYYxyyyyX", w! "xYXYxxyyyyX")]

private def layer27 : List WordState :=
  [(w! "XYYYxyyyy", w! "XYxxyyy"),
   (w! "YYYxyyyyX", w! "YXYxxyyyy"),
   (w! "YYYYXyyyx", w! "YXYxxyyyy"),
   (w! "xYYYYXyyy", w! "xYXYxxyyyyX")]

private def layer28 : List WordState :=
  [(w! "XYYYxyyyy", w! "YxxyyyX"),
   (w! "YYYxyyyyX", w! "XYxxyyy"),
   (w! "YYYYXyyyx", w! "XYxxyyy"),
   (w! "xYYYYXyyy", w! "YXYxxyyyy"),
   (w! "XYYYxyyyy", w! "XYxxYXyyyx")]

private def layer29 : List WordState :=
  [(w! "xYYYYXyyy", w! "XYxxyyy"),
   (w! "YYYxyyyyX", w! "YxxyyyX"),
   (w! "YYYYXyyyx", w! "YxxyyyX"),
   (w! "XYYYxyyyy", w! "YxxYXyyy"),
   (w! "YYYxyyyyX", w! "XYxxYXyyyx"),
   (w! "YYYYXyyyx", w! "XYxxYXyyyx")]

private def layer30 : List WordState :=
  [(w! "XYYYxyyyy", w! "xxYXyy"),
   (w! "xYYYYXyyy", w! "YxxyyyX"),
   (w! "YYYxyyyyX", w! "YxxYXyyy"),
   (w! "YYYYXyyyx", w! "YxxYXyyy"),
   (w! "xYYYYXyyy", w! "XYxxYXyyyx"),
   (w! "YYYYxyyyyXy", w! "XYxxYXyyyx")]

private def layer31 : List WordState :=
  [(w! "XYYYxyyyy", w! "yxxYXy"),
   (w! "YYYxyyyyX", w! "xxYXyy"),
   (w! "YYYYXyyyx", w! "xxYXyy"),
   (w! "xYYYYXyyy", w! "YxxYXyyy"),
   (w! "YYYYxyyyyXy", w! "YxxYXyyy"),
   (w! "YxYYYYXyyyy", w! "XYxxYXyyyx"),
   (w! "YYYYYxyyyyXyy", w! "XYxxYXyyyx")]

private def layer32 : List WordState :=
  [(w! "xYYYYXyyy", w! "xxYXyy"),
   (w! "XYYYxyyyy", w! "yyxxYX"),
   (w! "YYYxyyyyX", w! "yxxYXy"),
   (w! "YYYYXyyyx", w! "yxxYXy"),
   (w! "YYYYxyyyyXy", w! "xxYXyy"),
   (w! "YxYYYYXyyyy", w! "YxxYXyyy"),
   (w! "YYYYYxyyyyXyy", w! "YxxYXyyy"),
   (w! "YYxYYYYXyyyyy", w! "XYxxYXyyyx")]

private def layer33 : List WordState :=
  [(w! "xYYYYXyyy", w! "yxxYXy"),
   (w! "YYYxyyyyX", w! "yyxxYX"),
   (w! "YYYYXyyyx", w! "yyxxYX"),
   (w! "YxYYYYXyyyy", w! "xxYXyy"),
   (w! "YYYYxyyyyXy", w! "yxxYXy"),
   (w! "YYYYYxyyyyXyy", w! "xxYXyy"),
   (w! "YYxYYYYXyyyyy", w! "YxxYXyyy")]

private def layer34 : List WordState :=
  [(w! "xYYYYXyyy", w! "yyxxYX"),
   (w! "YxYYYYXyyyy", w! "yxxYXy"),
   (w! "YYxYYYYXyyyyy", w! "xxYXyy"),
   (w! "YYYxyyyyX", w! "yyxxYYYYYXyyy"),
   (w! "YYYYxyyyyXy", w! "yxxYYYYYXyyyy"),
   (w! "YYYYYxyyyyXyy", w! "xxYYYYYXyyyyy")]

private def layer35 : List WordState :=
  [(w! "xYYYYXyyy", w! "yyxxYYYYYXyyy"),
   (w! "YYxyyyyXY", w! "yyxxYYYYYXyyy"),
   (w! "YYYxyyyyX", w! "yxxYYYYYXyyyy"),
   (w! "YxYYYYXyyyy", w! "yxxYYYYYXyyyy"),
   (w! "YYYYxyyyyXy", w! "xxYYYYYXyyyyy"),
   (w! "YYxYYYYXyyyyy", w! "xxYYYYYXyyyyy")]

private def layer36 : List WordState :=
  [(w! "xYYYYXyyy", w! "yxxYYYYYXyyyy"),
   (w! "yxYYYYXyy", w! "yyxxYYYYYXyyy"),
   (w! "YxyyyyXYY", w! "yyxxYYYYYXyyy"),
   (w! "YYxyyyyXY", w! "yxxYYYYYXyyyy"),
   (w! "YYYxyyyyX", w! "xxYYYYYXyyyyy"),
   (w! "YxYYYYXyyyy", w! "xxYYYYYXyyyyy")]

private def layer37 : List WordState :=
  [(w! "xyyyyXYYY", w! "yyxxYYYYYXyyy"),
   (w! "xYYYYXyyy", w! "xxYYYYYXyyyyy"),
   (w! "yxYYYYXyy", w! "yxxYYYYYXyyyy"),
   (w! "yyxYYYYXy", w! "yyxxYYYYYXyyy"),
   (w! "YxyyyyXYY", w! "yxxYYYYYXyyyy"),
   (w! "YYxyyyyXY", w! "xxYYYYYXyyyyy")]

private def layer38 : List WordState :=
  [(w! "xyyyyXYYY", w! "yxxYYYYYXyyyy"),
   (w! "yxYYYYXyy", w! "xxYYYYYXyyyyy"),
   (w! "yyxYYYYXy", w! "yxxYYYYYXyyyy"),
   (w! "yyyxYYYYX", w! "yyxxYYYYYXyyy"),
   (w! "yyyyXYYYx", w! "yyxxYYYYYXyyy"),
   (w! "YxyyyyXYY", w! "xxYYYYYXyyyyy")]

private def layer39 : List WordState :=
  [(w! "xyyyyXYYY", w! "xxYYYYYXyyyyy"),
   (w! "XyyyxYYYY", w! "yyxxYYYYYXyyy"),
   (w! "yyxYYYYXy", w! "xxYYYYYXyyyyy"),
   (w! "yyyxYYYYX", w! "yxxYYYYYXyyyy"),
   (w! "yyyyXYYYx", w! "yxxYYYYYXyyyy")]

private def layer40 : List WordState :=
  [(w! "XyyyxYYYY", w! "yxxYYYYYXyyyy"),
   (w! "yyyxYYYYX", w! "xxYYYYYXyyyyy"),
   (w! "yyyyXYYYx", w! "xxYYYYYXyyyyy")]

private def layer41 : List WordState :=
  [(w! "XyyyxYYYY", w! "xxYYYYYXyyyyy")]

private def rest41 := layer41 :: []
private def rest40 := layer40 :: rest41
private def rest39 := layer39 :: rest40
private def rest38 := layer38 :: rest39
private def rest37 := layer37 :: rest38
private def rest36 := layer36 :: rest37
private def rest35 := layer35 :: rest36
private def rest34 := layer34 :: rest35
private def rest33 := layer33 :: rest34
private def rest32 := layer32 :: rest33
private def rest31 := layer31 :: rest32
private def rest30 := layer30 :: rest31
private def rest29 := layer29 :: rest30
private def rest28 := layer28 :: rest29
private def rest27 := layer27 :: rest28
private def rest26 := layer26 :: rest27
private def rest25 := layer25 :: rest26
private def rest24 := layer24 :: rest25
private def rest23 := layer23 :: rest24
private def rest22 := layer22 :: rest23
private def rest21 := layer21 :: rest22
private def rest20 := layer20 :: rest21
private def rest19 := layer19 :: rest20
private def rest18 := layer18 :: rest19
private def rest17 := layer17 :: rest18
private def rest16 := layer16 :: rest17
private def rest15 := layer15 :: rest16
private def rest14 := layer14 :: rest15
private def rest13 := layer13 :: rest14
private def rest12 := layer12 :: rest13
private def rest11 := layer11 :: rest12
private def rest10 := layer10 :: rest11
private def rest9 := layer9 :: rest10
private def rest8 := layer8 :: rest9
private def rest7 := layer7 :: rest8
private def rest6 := layer6 :: rest7
private def rest5 := layer5 :: rest6
private def rest4 := layer4 :: rest5
private def rest3 := layer3 :: rest4
private def rest2 := layer2 :: rest3
private def rest1 := layer1 :: rest2
private def rest0 := layer0 :: rest1

def recordedLayers := rest1

theorem layer_count : recordedLayers.length = 41 := by decide +kernel

private def c27_41 : Counts := layer41.zip [1]
private theorem ok27_41 : table 27 rest41 = c27_41 := by
  decide +kernel

private def c27_40 : Counts := layer40.zip [1, 1, 1]
private theorem ok27_40 : table 27 rest40 = c27_40 := by
  change propagate 27 layer40 (table 27 rest41) = _
  rw [ok27_41]
  decide +kernel

private def c27_39 : Counts := layer39.zip [2, 1, 1, 2, 2]
private theorem ok27_39 : table 27 rest39 = c27_39 := by
  change propagate 27 layer39 (table 27 rest40) = _
  rw [ok27_40]
  decide +kernel

private def c27_38 : Counts := layer38.zip [6, 1, 3, 3, 3, 3]
private theorem ok27_38 : table 27 rest38 = c27_38 := by
  change propagate 27 layer38 (table 27 rest39) = _
  rw [ok27_39]
  decide +kernel

private def c27_37 : Counts := layer37.zip [12, 1, 4, 6, 12, 4]
private theorem ok27_37 : table 27 rest37 = c27_37 := by
  change propagate 27 layer37 (table 27 rest38) = _
  rw [ok27_38]
  decide +kernel

private def c27_36 : Counts := layer36.zip [5, 10, 30, 20, 5, 1]
private theorem ok27_36 : table 27 rest36 = c27_36 := by
  change propagate 27 layer36 (table 27 rest37) = _
  rw [ok27_37]
  decide +kernel

private def c27_35 : Counts := layer35.zip [15, 60, 30, 6, 6, 1]
private theorem ok27_35 : table 27 rest35 = c27_35 := by
  change propagate 27 layer35 (table 27 rest36) = _
  rw [ok27_36]
  decide +kernel

private def c27_34 : Counts := layer34.zip [15, 6, 1, 105, 42, 7]
private theorem ok27_34 : table 27 rest34 = c27_34 := by
  change propagate 27 layer34 (table 27 rest35) = _
  rw [ok27_35]
  decide +kernel

private def c27_33 : Counts := layer33.zip [21, 120, 15, 7, 48, 8, 1]
private theorem ok27_33 : table 27 rest33 = c27_33 := by
  change propagate 27 layer33 (table 27 rest34) = _
  rw [ok27_34]
  decide +kernel

private def c27_32 : Counts := layer32.zip [28, 135, 189, 36, 63, 8, 9, 1]
private theorem ok27_32 : table 27 rest32 = c27_32 := by
  change propagate 27 layer32 (table 27 rest33) = _
  rw [ok27_33]
  decide +kernel

private def c27_31 : Counts := layer31.zip [360, 280, 64, 36, 80, 9, 10]
private theorem ok27_31 : table 27 rest31 = c27_31 := by
  change propagate 27 layer31 (table 27 rest32) = _
  rw [ok27_32]
  decide +kernel

private def c27_30 : Counts := layer30.zip [704, 36, 396, 100, 45, 99]
private theorem ok27_30 : table 27 rest30 = c27_30 := by
  change propagate 27 layer30 (table 27 rest31) = _
  rw [ok27_31]
  decide +kernel

private def c27_29 : Counts := layer29.zip [36, 432, 36, 1200, 540, 145]
private theorem ok27_29 : table 27 rest29 = c27_29 := by
  change propagate 27 layer29 (table 27 rest30) = _
  rw [ok27_30]
  decide +kernel

private def c27_28 : Counts := layer28.zip [468, 468, 217, 36, 1885]
private theorem ok27_28 : table 27 rest28 = c27_28 := by
  change propagate 27 layer28 (table 27 rest29) = _
  rw [ok27_29]
  decide +kernel

private def c27_27 : Counts := layer27.zip [3038, 504, 253, 36]
private theorem ok27_27 : table 27 rest27 = c27_27 := by
  change propagate 27 layer27 (table 27 rest28) = _
  rw [ok27_28]
  decide +kernel

private def c27_26 : Counts := layer26.zip [36, 253, 3795, 540]
private theorem ok27_26 : table 27 rest26 = c27_26 := by
  change propagate 27 layer26 (table 27 rest27) = _
  rw [ok27_27]
  decide +kernel

private def c27_25 : Counts := layer25.zip [4048, 576, 289, 36]
private theorem ok27_25 : table 27 rest25 = c27_25 := by
  change propagate 27 layer25 (table 27 rest26) = _
  rw [ok27_26]
  decide +kernel

private def c27_24 : Counts := layer24.zip [4913, 612, 325, 36]
private theorem ok27_24 : table 27 rest24 = c27_24 := by
  change propagate 27 layer24 (table 27 rest25) = _
  rw [ok27_25]
  decide +kernel

private def c27_23 : Counts := layer23.zip [36, 325, 5850, 648]
private theorem ok27_23 : table 27 rest23 = c27_23 := by
  change propagate 27 layer23 (table 27 rest24) = _
  rw [ok27_24]
  decide +kernel

private def c27_22 : Counts := layer22.zip [6175, 684, 361, 36]
private theorem ok27_22 : table 27 rest22 = c27_22 := by
  change propagate 27 layer22 (table 27 rest23) = _
  rw [ok27_23]
  decide +kernel

private def c27_21 : Counts := layer21.zip [7220, 36, 720, 397, 36]
private theorem ok27_21 : table 27 rest21 = c27_21 := by
  change propagate 27 layer21 (table 27 rest22) = _
  rw [ok27_22]
  decide +kernel

private def c27_20 : Counts := layer20.zip [36, 756, 36, 8337, 756, 433]
private theorem ok27_20 : table 27 rest20 = c27_20 := by
  change propagate 27 layer20 (table 27 rest21) = _
  rw [ok27_21]
  decide +kernel

private def c27_19 : Counts := layer19.zip [792, 792, 505, 36, 9526]
private theorem ok27_19 : table 27 rest19 = c27_19 := by
  change propagate 27 layer19 (table 27 rest20) = _
  rw [ok27_20]
  decide +kernel

private def c27_18 : Counts := layer18.zip [11615, 828, 541]
private theorem ok27_18 : table 27 rest18 = c27_18 := by
  change propagate 27 layer18 (table 27 rest19) = _
  rw [ok27_19]
  decide +kernel

private def c27_17 : Counts := layer17.zip [541, 12984]
private theorem ok27_17 : table 27 rest17 = c27_17 := by
  change propagate 27 layer17 (table 27 rest18) = _
  rw [ok27_18]
  decide +kernel

private def c27_16 : Counts := layer16.zip [13525, 541]
private theorem ok27_16 : table 27 rest16 = c27_16 := by
  change propagate 27 layer16 (table 27 rest17) = _
  rw [ok27_17]
  decide +kernel

private def c27_15 : Counts := layer15.zip [14066, 541]
private theorem ok27_15 : table 27 rest15 = c27_15 := by
  change propagate 27 layer15 (table 27 rest16) = _
  rw [ok27_16]
  decide +kernel

private def c27_14 : Counts := layer14.zip [14607, 541]
private theorem ok27_14 : table 27 rest14 = c27_14 := by
  change propagate 27 layer14 (table 27 rest15) = _
  rw [ok27_15]
  decide +kernel

private def c27_13 : Counts := layer13.zip [15148, 541]
private theorem ok27_13 : table 27 rest13 = c27_13 := by
  change propagate 27 layer13 (table 27 rest14) = _
  rw [ok27_14]
  decide +kernel

private def c27_12 : Counts := layer12.zip [541, 15689]
private theorem ok27_12 : table 27 rest12 = c27_12 := by
  change propagate 27 layer12 (table 27 rest13) = _
  rw [ok27_13]
  decide +kernel

private def c27_11 : Counts := layer11.zip [16230, 541, 541]
private theorem ok27_11 : table 27 rest11 = c27_11 := by
  change propagate 27 layer11 (table 27 rest12) = _
  rw [ok27_12]
  decide +kernel

private def c27_10 : Counts := layer10.zip [16771, 16771, 1082]
private theorem ok27_10 : table 27 rest10 = c27_10 := by
  change propagate 27 layer10 (table 27 rest11) = _
  rw [ok27_11]
  decide +kernel

private def c27_9 : Counts := layer9.zip [1082, 34624]
private theorem ok27_9 : table 27 rest9 = c27_9 := by
  change propagate 27 layer9 (table 27 rest10) = _
  rw [ok27_10]
  decide +kernel

private def c27_8 : Counts := layer8.zip [35706, 1082, 34624]
private theorem ok27_8 : table 27 rest8 = c27_8 := by
  change propagate 27 layer8 (table 27 rest9) = _
  rw [ok27_9]
  decide +kernel

private def c27_7 : Counts := layer7.zip [36788, 34624]
private theorem ok27_7 : table 27 rest7 = c27_7 := by
  change propagate 27 layer7 (table 27 rest8) = _
  rw [ok27_8]
  decide +kernel

private def c28_41 : Counts := layer41.zip [1]
private theorem ok28_41 : table 28 rest41 = c28_41 := by
  decide +kernel

private def c28_40 : Counts := layer40.zip [1, 1, 1]
private theorem ok28_40 : table 28 rest40 = c28_40 := by
  change propagate 28 layer40 (table 28 rest41) = _
  rw [ok28_41]
  decide +kernel

private def c28_39 : Counts := layer39.zip [2, 1, 1, 2, 2]
private theorem ok28_39 : table 28 rest39 = c28_39 := by
  change propagate 28 layer39 (table 28 rest40) = _
  rw [ok28_40]
  decide +kernel

private def c28_38 : Counts := layer38.zip [6, 1, 3, 3, 3, 3]
private theorem ok28_38 : table 28 rest38 = c28_38 := by
  change propagate 28 layer38 (table 28 rest39) = _
  rw [ok28_39]
  decide +kernel

private def c28_37 : Counts := layer37.zip [12, 1, 4, 6, 12, 4]
private theorem ok28_37 : table 28 rest37 = c28_37 := by
  change propagate 28 layer37 (table 28 rest38) = _
  rw [ok28_38]
  decide +kernel

private def c28_36 : Counts := layer36.zip [5, 10, 30, 20, 5, 1]
private theorem ok28_36 : table 28 rest36 = c28_36 := by
  change propagate 28 layer36 (table 28 rest37) = _
  rw [ok28_37]
  decide +kernel

private def c28_35 : Counts := layer35.zip [15, 60, 30, 6, 6, 1]
private theorem ok28_35 : table 28 rest35 = c28_35 := by
  change propagate 28 layer35 (table 28 rest36) = _
  rw [ok28_36]
  decide +kernel

private def c28_34 : Counts := layer34.zip [15, 6, 1, 105, 42, 7]
private theorem ok28_34 : table 28 rest34 = c28_34 := by
  change propagate 28 layer34 (table 28 rest35) = _
  rw [ok28_35]
  decide +kernel

private def c28_33 : Counts := layer33.zip [21, 120, 15, 7, 48, 8, 1]
private theorem ok28_33 : table 28 rest33 = c28_33 := by
  change propagate 28 layer33 (table 28 rest34) = _
  rw [ok28_34]
  decide +kernel

private def c28_32 : Counts := layer32.zip [28, 135, 189, 36, 63, 8, 9, 1]
private theorem ok28_32 : table 28 rest32 = c28_32 := by
  change propagate 28 layer32 (table 28 rest33) = _
  rw [ok28_33]
  decide +kernel

private def c28_31 : Counts := layer31.zip [360, 280, 64, 36, 80, 9, 10]
private theorem ok28_31 : table 28 rest31 = c28_31 := by
  change propagate 28 layer31 (table 28 rest32) = _
  rw [ok28_32]
  decide +kernel

private def c28_30 : Counts := layer30.zip [704, 36, 396, 100, 45, 99]
private theorem ok28_30 : table 28 rest30 = c28_30 := by
  change propagate 28 layer30 (table 28 rest31) = _
  rw [ok28_31]
  decide +kernel

private def c28_29 : Counts := layer29.zip [36, 432, 36, 1200, 540, 145]
private theorem ok28_29 : table 28 rest29 = c28_29 := by
  change propagate 28 layer29 (table 28 rest30) = _
  rw [ok28_30]
  decide +kernel

private def c28_28 : Counts := layer28.zip [468, 468, 217, 36, 1885]
private theorem ok28_28 : table 28 rest28 = c28_28 := by
  change propagate 28 layer28 (table 28 rest29) = _
  rw [ok28_29]
  decide +kernel

private def c28_27 : Counts := layer27.zip [3038, 504, 253, 36]
private theorem ok28_27 : table 28 rest27 = c28_27 := by
  change propagate 28 layer27 (table 28 rest28) = _
  rw [ok28_28]
  decide +kernel

private def c28_26 : Counts := layer26.zip [36, 253, 3795, 540]
private theorem ok28_26 : table 28 rest26 = c28_26 := by
  change propagate 28 layer26 (table 28 rest27) = _
  rw [ok28_27]
  decide +kernel

private def c28_25 : Counts := layer25.zip [4048, 576, 289, 36]
private theorem ok28_25 : table 28 rest25 = c28_25 := by
  change propagate 28 layer25 (table 28 rest26) = _
  rw [ok28_26]
  decide +kernel

private def c28_24 : Counts := layer24.zip [4913, 612, 325, 36]
private theorem ok28_24 : table 28 rest24 = c28_24 := by
  change propagate 28 layer24 (table 28 rest25) = _
  rw [ok28_25]
  decide +kernel

private def c28_23 : Counts := layer23.zip [36, 325, 5850, 648]
private theorem ok28_23 : table 28 rest23 = c28_23 := by
  change propagate 28 layer23 (table 28 rest24) = _
  rw [ok28_24]
  decide +kernel

private def c28_22 : Counts := layer22.zip [6175, 684, 361, 36]
private theorem ok28_22 : table 28 rest22 = c28_22 := by
  change propagate 28 layer22 (table 28 rest23) = _
  rw [ok28_23]
  decide +kernel

private def c28_21 : Counts := layer21.zip [7220, 36, 720, 397, 36]
private theorem ok28_21 : table 28 rest21 = c28_21 := by
  change propagate 28 layer21 (table 28 rest22) = _
  rw [ok28_22]
  decide +kernel

private def c28_20 : Counts := layer20.zip [36, 756, 36, 8337, 756, 433]
private theorem ok28_20 : table 28 rest20 = c28_20 := by
  change propagate 28 layer20 (table 28 rest21) = _
  rw [ok28_21]
  decide +kernel

private def c28_19 : Counts := layer19.zip [792, 792, 505, 36, 9526]
private theorem ok28_19 : table 28 rest19 = c28_19 := by
  change propagate 28 layer19 (table 28 rest20) = _
  rw [ok28_20]
  decide +kernel

private def c28_18 : Counts := layer18.zip [11615, 828, 541]
private theorem ok28_18 : table 28 rest18 = c28_18 := by
  change propagate 28 layer18 (table 28 rest19) = _
  rw [ok28_19]
  decide +kernel

private def c28_17 : Counts := layer17.zip [541, 12984]
private theorem ok28_17 : table 28 rest17 = c28_17 := by
  change propagate 28 layer17 (table 28 rest18) = _
  rw [ok28_18]
  decide +kernel

private def c28_16 : Counts := layer16.zip [13525, 541]
private theorem ok28_16 : table 28 rest16 = c28_16 := by
  change propagate 28 layer16 (table 28 rest17) = _
  rw [ok28_17]
  decide +kernel

private def c28_15 : Counts := layer15.zip [14066, 541]
private theorem ok28_15 : table 28 rest15 = c28_15 := by
  change propagate 28 layer15 (table 28 rest16) = _
  rw [ok28_16]
  decide +kernel

private def c28_14 : Counts := layer14.zip [14607, 541]
private theorem ok28_14 : table 28 rest14 = c28_14 := by
  change propagate 28 layer14 (table 28 rest15) = _
  rw [ok28_15]
  decide +kernel

private def c28_13 : Counts := layer13.zip [15148, 541]
private theorem ok28_13 : table 28 rest13 = c28_13 := by
  change propagate 28 layer13 (table 28 rest14) = _
  rw [ok28_14]
  decide +kernel

private def c28_12 : Counts := layer12.zip [541, 15689]
private theorem ok28_12 : table 28 rest12 = c28_12 := by
  change propagate 28 layer12 (table 28 rest13) = _
  rw [ok28_13]
  decide +kernel

private def c28_11 : Counts := layer11.zip [16230, 541, 541]
private theorem ok28_11 : table 28 rest11 = c28_11 := by
  change propagate 28 layer11 (table 28 rest12) = _
  rw [ok28_12]
  decide +kernel

private def c28_10 : Counts := layer10.zip [16771, 16771, 1082]
private theorem ok28_10 : table 28 rest10 = c28_10 := by
  change propagate 28 layer10 (table 28 rest11) = _
  rw [ok28_11]
  decide +kernel

private def c28_9 : Counts := layer9.zip [1082, 34624]
private theorem ok28_9 : table 28 rest9 = c28_9 := by
  change propagate 28 layer9 (table 28 rest10) = _
  rw [ok28_10]
  decide +kernel

private def c28_8 : Counts := layer8.zip [35706, 1082, 34624]
private theorem ok28_8 : table 28 rest8 = c28_8 := by
  change propagate 28 layer8 (table 28 rest9) = _
  rw [ok28_9]
  decide +kernel

private def c28_7 : Counts := layer7.zip [36788, 34624]
private theorem ok28_7 : table 28 rest7 = c28_7 := by
  change propagate 28 layer7 (table 28 rest8) = _
  rw [ok28_8]
  decide +kernel

private def c28_6 : Counts := layer6.zip [36788, 34624, 34624]
private theorem ok28_6 : table 28 rest6 = c28_6 := by
  change propagate 28 layer6 (table 28 rest7) = _
  rw [ok28_7]
  decide +kernel

private def c28_5 : Counts := layer5.zip [36788, 34624, 0]
private theorem ok28_5 : table 28 rest5 = c28_5 := by
  change propagate 28 layer5 (table 28 rest6) = _
  rw [ok28_6]
  decide +kernel

private def c28_4 : Counts := layer4.zip [71412, 0]
private theorem ok28_4 : table 28 rest4 = c28_4 := by
  change propagate 28 layer4 (table 28 rest5) = _
  rw [ok28_5]
  decide +kernel

private def c28_3 : Counts := layer3.zip [71412, 0]
private theorem ok28_3 : table 28 rest3 = c28_3 := by
  change propagate 28 layer3 (table 28 rest4) = _
  rw [ok28_4]
  decide +kernel

private def c28_2 : Counts := layer2.zip [71412]
private theorem ok28_2 : table 28 rest2 = c28_2 := by
  change propagate 28 layer2 (table 28 rest3) = _
  rw [ok28_3]
  decide +kernel

private def c28_1 : Counts := layer1.zip [71412]
private theorem ok28_1 : table 28 rest1 = c28_1 := by
  change propagate 28 layer1 (table 28 rest2) = _
  rw [ok28_2]
  decide +kernel

private def c28_0 : Counts := layer0.zip [71412]
private theorem ok28_0 : table 28 rest0 = c28_0 := by
  change propagate 28 layer0 (table 28 rest1) = _
  rw [ok28_1]
  decide +kernel

private def c29_41 : Counts := layer41.zip [1]
private theorem ok29_41 : table 29 rest41 = c29_41 := by
  decide +kernel

private def c29_40 : Counts := layer40.zip [1, 1, 1]
private theorem ok29_40 : table 29 rest40 = c29_40 := by
  change propagate 29 layer40 (table 29 rest41) = _
  rw [ok29_41]
  decide +kernel

private def c29_39 : Counts := layer39.zip [2, 1, 1, 2, 2]
private theorem ok29_39 : table 29 rest39 = c29_39 := by
  change propagate 29 layer39 (table 29 rest40) = _
  rw [ok29_40]
  decide +kernel

private def c29_38 : Counts := layer38.zip [6, 1, 3, 3, 3, 3]
private theorem ok29_38 : table 29 rest38 = c29_38 := by
  change propagate 29 layer38 (table 29 rest39) = _
  rw [ok29_39]
  decide +kernel

private def c29_37 : Counts := layer37.zip [12, 1, 4, 6, 12, 4]
private theorem ok29_37 : table 29 rest37 = c29_37 := by
  change propagate 29 layer37 (table 29 rest38) = _
  rw [ok29_38]
  decide +kernel

private def c29_36 : Counts := layer36.zip [5, 10, 30, 20, 5, 1]
private theorem ok29_36 : table 29 rest36 = c29_36 := by
  change propagate 29 layer36 (table 29 rest37) = _
  rw [ok29_37]
  decide +kernel

private def c29_35 : Counts := layer35.zip [15, 60, 30, 6, 6, 1]
private theorem ok29_35 : table 29 rest35 = c29_35 := by
  change propagate 29 layer35 (table 29 rest36) = _
  rw [ok29_36]
  decide +kernel

private def c29_34 : Counts := layer34.zip [15, 6, 1, 105, 42, 7]
private theorem ok29_34 : table 29 rest34 = c29_34 := by
  change propagate 29 layer34 (table 29 rest35) = _
  rw [ok29_35]
  decide +kernel

private def c29_33 : Counts := layer33.zip [21, 120, 15, 7, 48, 8, 1]
private theorem ok29_33 : table 29 rest33 = c29_33 := by
  change propagate 29 layer33 (table 29 rest34) = _
  rw [ok29_34]
  decide +kernel

private def c29_32 : Counts := layer32.zip [28, 135, 189, 36, 63, 8, 9, 1]
private theorem ok29_32 : table 29 rest32 = c29_32 := by
  change propagate 29 layer32 (table 29 rest33) = _
  rw [ok29_33]
  decide +kernel

private def c29_31 : Counts := layer31.zip [360, 280, 64, 36, 80, 9, 10]
private theorem ok29_31 : table 29 rest31 = c29_31 := by
  change propagate 29 layer31 (table 29 rest32) = _
  rw [ok29_32]
  decide +kernel

private def c29_30 : Counts := layer30.zip [704, 36, 396, 100, 45, 99]
private theorem ok29_30 : table 29 rest30 = c29_30 := by
  change propagate 29 layer30 (table 29 rest31) = _
  rw [ok29_31]
  decide +kernel

private def c29_29 : Counts := layer29.zip [36, 432, 36, 1200, 540, 145]
private theorem ok29_29 : table 29 rest29 = c29_29 := by
  change propagate 29 layer29 (table 29 rest30) = _
  rw [ok29_30]
  decide +kernel

private def c29_28 : Counts := layer28.zip [468, 468, 217, 36, 1885]
private theorem ok29_28 : table 29 rest28 = c29_28 := by
  change propagate 29 layer28 (table 29 rest29) = _
  rw [ok29_29]
  decide +kernel

private def c29_27 : Counts := layer27.zip [3038, 504, 253, 36]
private theorem ok29_27 : table 29 rest27 = c29_27 := by
  change propagate 29 layer27 (table 29 rest28) = _
  rw [ok29_28]
  decide +kernel

private def c29_26 : Counts := layer26.zip [36, 253, 3795, 540]
private theorem ok29_26 : table 29 rest26 = c29_26 := by
  change propagate 29 layer26 (table 29 rest27) = _
  rw [ok29_27]
  decide +kernel

private def c29_25 : Counts := layer25.zip [4048, 576, 289, 36]
private theorem ok29_25 : table 29 rest25 = c29_25 := by
  change propagate 29 layer25 (table 29 rest26) = _
  rw [ok29_26]
  decide +kernel

private def c29_24 : Counts := layer24.zip [4913, 612, 325, 36]
private theorem ok29_24 : table 29 rest24 = c29_24 := by
  change propagate 29 layer24 (table 29 rest25) = _
  rw [ok29_25]
  decide +kernel

private def c29_23 : Counts := layer23.zip [36, 325, 5850, 648]
private theorem ok29_23 : table 29 rest23 = c29_23 := by
  change propagate 29 layer23 (table 29 rest24) = _
  rw [ok29_24]
  decide +kernel

private def c29_22 : Counts := layer22.zip [6175, 684, 361, 36]
private theorem ok29_22 : table 29 rest22 = c29_22 := by
  change propagate 29 layer22 (table 29 rest23) = _
  rw [ok29_23]
  decide +kernel

private def c29_21 : Counts := layer21.zip [7220, 36, 720, 397, 36]
private theorem ok29_21 : table 29 rest21 = c29_21 := by
  change propagate 29 layer21 (table 29 rest22) = _
  rw [ok29_22]
  decide +kernel

private def c29_20 : Counts := layer20.zip [36, 756, 36, 8337, 756, 433]
private theorem ok29_20 : table 29 rest20 = c29_20 := by
  change propagate 29 layer20 (table 29 rest21) = _
  rw [ok29_21]
  decide +kernel

private def c29_19 : Counts := layer19.zip [792, 792, 505, 36, 9526]
private theorem ok29_19 : table 29 rest19 = c29_19 := by
  change propagate 29 layer19 (table 29 rest20) = _
  rw [ok29_20]
  decide +kernel

private def c29_18 : Counts := layer18.zip [11615, 828, 541]
private theorem ok29_18 : table 29 rest18 = c29_18 := by
  change propagate 29 layer18 (table 29 rest19) = _
  rw [ok29_19]
  decide +kernel

private def c29_17 : Counts := layer17.zip [541, 12984]
private theorem ok29_17 : table 29 rest17 = c29_17 := by
  change propagate 29 layer17 (table 29 rest18) = _
  rw [ok29_18]
  decide +kernel

private def c29_16 : Counts := layer16.zip [13525, 541]
private theorem ok29_16 : table 29 rest16 = c29_16 := by
  change propagate 29 layer16 (table 29 rest17) = _
  rw [ok29_17]
  decide +kernel

private def c29_15 : Counts := layer15.zip [14066, 541]
private theorem ok29_15 : table 29 rest15 = c29_15 := by
  change propagate 29 layer15 (table 29 rest16) = _
  rw [ok29_16]
  decide +kernel

private def c29_14 : Counts := layer14.zip [14607, 541]
private theorem ok29_14 : table 29 rest14 = c29_14 := by
  change propagate 29 layer14 (table 29 rest15) = _
  rw [ok29_15]
  decide +kernel

private def c29_13 : Counts := layer13.zip [15148, 541]
private theorem ok29_13 : table 29 rest13 = c29_13 := by
  change propagate 29 layer13 (table 29 rest14) = _
  rw [ok29_14]
  decide +kernel

private def c29_12 : Counts := layer12.zip [541, 15689]
private theorem ok29_12 : table 29 rest12 = c29_12 := by
  change propagate 29 layer12 (table 29 rest13) = _
  rw [ok29_13]
  decide +kernel

private def c29_11 : Counts := layer11.zip [16230, 541, 541]
private theorem ok29_11 : table 29 rest11 = c29_11 := by
  change propagate 29 layer11 (table 29 rest12) = _
  rw [ok29_12]
  decide +kernel

private def c29_10 : Counts := layer10.zip [16771, 16771, 1082]
private theorem ok29_10 : table 29 rest10 = c29_10 := by
  change propagate 29 layer10 (table 29 rest11) = _
  rw [ok29_11]
  decide +kernel

private def c29_9 : Counts := layer9.zip [1082, 34624]
private theorem ok29_9 : table 29 rest9 = c29_9 := by
  change propagate 29 layer9 (table 29 rest10) = _
  rw [ok29_10]
  decide +kernel

private def c29_8 : Counts := layer8.zip [35706, 1082, 34624]
private theorem ok29_8 : table 29 rest8 = c29_8 := by
  change propagate 29 layer8 (table 29 rest9) = _
  rw [ok29_9]
  decide +kernel

private def c29_7 : Counts := layer7.zip [36788, 34624]
private theorem ok29_7 : table 29 rest7 = c29_7 := by
  change propagate 29 layer7 (table 29 rest8) = _
  rw [ok29_8]
  decide +kernel

private def c29_6 : Counts := layer6.zip [36788, 34624, 34624]
private theorem ok29_6 : table 29 rest6 = c29_6 := by
  change propagate 29 layer6 (table 29 rest7) = _
  rw [ok29_7]
  decide +kernel

private def c29_5 : Counts := layer5.zip [36788, 34624, 34624]
private theorem ok29_5 : table 29 rest5 = c29_5 := by
  change propagate 29 layer5 (table 29 rest6) = _
  rw [ok29_6]
  decide +kernel

private def c29_4 : Counts := layer4.zip [71412, 34624]
private theorem ok29_4 : table 29 rest4 = c29_4 := by
  change propagate 29 layer4 (table 29 rest5) = _
  rw [ok29_5]
  decide +kernel

private def c29_3 : Counts := layer3.zip [71412, 34624]
private theorem ok29_3 : table 29 rest3 = c29_3 := by
  change propagate 29 layer3 (table 29 rest4) = _
  rw [ok29_4]
  decide +kernel

private def c29_2 : Counts := layer2.zip [106036]
private theorem ok29_2 : table 29 rest2 = c29_2 := by
  change propagate 29 layer2 (table 29 rest3) = _
  rw [ok29_3]
  decide +kernel

private def c29_1 : Counts := layer1.zip [106036]
private theorem ok29_1 : table 29 rest1 = c29_1 := by
  change propagate 29 layer1 (table 29 rest2) = _
  rw [ok29_2]
  decide +kernel

private def c29_0 : Counts := layer0.zip [106036]
private theorem ok29_0 : table 29 rest0 = c29_0 := by
  change propagate 29 layer0 (table 29 rest1) = _
  rw [ok29_1]
  decide +kernel

theorem recorded_counts : countFrom 28 recordedLayers ak3 = 71412 ∧ countFrom 29 recordedLayers ak3 = 106036 := by
  have c : ways (table 28 (layer0 :: recordedLayers)) ak3 = 71412 ∧
      ways (table 29 (layer0 :: recordedLayers)) ak3 = 106036 := by
    change ways (table 28 rest0) ak3 = _ ∧ ways (table 29 rest0) ak3 = _
    rw [ok28_0, ok29_0]
    decide +kernel
  simpa only [table_correct, ite_eq_left (by decide +kernel : ak3 ∈ layer0)] using c

def suffixLayers := rest8
theorem suffix_depths : suffixLayers.length = 34 := by decide +kernel
theorem shared_suffix_count :
    countFrom 27 suffixLayers (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX") = 34624 := by
  let j : WordState := (w! "YXYYxyyyyyX", w! "xxYYYYYXYxyyyyyX")
  have c : ways (table 27 (layer7 :: suffixLayers)) j = 34624 := by
    change ways (table 27 rest7) j = _
    rw [ok27_7]
    decide +kernel
  simpa only [table_correct, ite_eq_left (by decide +kernel : j ∈ layer7)] using c

end Candidate.AK3Peak.FixedS
