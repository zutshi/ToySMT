(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

;------------------------------
;00 01 02 | 03 04 05 | 06 07 08
;10 11 12 | 13 14 15 | 16 17 18
;20 21 22 | 23 24 25 | 26 27 28
;------------------------------
;30 31 32 | 33 34 35 | 36 37 38
;40 41 42 | 43 44 45 | 46 47 48
;50 51 52 | 53 54 55 | 56 57 58
;------------------------------
;60 61 62 | 63 64 65 | 66 67 68
;70 71 72 | 73 74 75 | 76 77 78
;80 81 82 | 83 84 85 | 86 87 88
;------------------------------


(declare-fun cell00 () (_ BitVec 4))
(declare-fun cell01 () (_ BitVec 4))
(declare-fun cell02 () (_ BitVec 4))
(declare-fun cell03 () (_ BitVec 4))
(declare-fun cell04 () (_ BitVec 4))
(declare-fun cell05 () (_ BitVec 4))
(declare-fun cell06 () (_ BitVec 4))
(declare-fun cell07 () (_ BitVec 4))
(declare-fun cell08 () (_ BitVec 4))

(declare-fun cell10 () (_ BitVec 4))
(declare-fun cell11 () (_ BitVec 4))
(declare-fun cell12 () (_ BitVec 4))
(declare-fun cell13 () (_ BitVec 4))
(declare-fun cell14 () (_ BitVec 4))
(declare-fun cell15 () (_ BitVec 4))
(declare-fun cell16 () (_ BitVec 4))
(declare-fun cell17 () (_ BitVec 4))
(declare-fun cell18 () (_ BitVec 4))

(declare-fun cell20 () (_ BitVec 4))
(declare-fun cell21 () (_ BitVec 4))
(declare-fun cell22 () (_ BitVec 4))
(declare-fun cell23 () (_ BitVec 4))
(declare-fun cell24 () (_ BitVec 4))
(declare-fun cell25 () (_ BitVec 4))
(declare-fun cell26 () (_ BitVec 4))
(declare-fun cell27 () (_ BitVec 4))
(declare-fun cell28 () (_ BitVec 4))

(declare-fun cell30 () (_ BitVec 4))
(declare-fun cell31 () (_ BitVec 4))
(declare-fun cell32 () (_ BitVec 4))
(declare-fun cell33 () (_ BitVec 4))
(declare-fun cell34 () (_ BitVec 4))
(declare-fun cell35 () (_ BitVec 4))
(declare-fun cell36 () (_ BitVec 4))
(declare-fun cell37 () (_ BitVec 4))
(declare-fun cell38 () (_ BitVec 4))

(declare-fun cell40 () (_ BitVec 4))
(declare-fun cell41 () (_ BitVec 4))
(declare-fun cell42 () (_ BitVec 4))
(declare-fun cell43 () (_ BitVec 4))
(declare-fun cell44 () (_ BitVec 4))
(declare-fun cell45 () (_ BitVec 4))
(declare-fun cell46 () (_ BitVec 4))
(declare-fun cell47 () (_ BitVec 4))
(declare-fun cell48 () (_ BitVec 4))

(declare-fun cell50 () (_ BitVec 4))
(declare-fun cell51 () (_ BitVec 4))
(declare-fun cell52 () (_ BitVec 4))
(declare-fun cell53 () (_ BitVec 4))
(declare-fun cell54 () (_ BitVec 4))
(declare-fun cell55 () (_ BitVec 4))
(declare-fun cell56 () (_ BitVec 4))
(declare-fun cell57 () (_ BitVec 4))
(declare-fun cell58 () (_ BitVec 4))

(declare-fun cell60 () (_ BitVec 4))
(declare-fun cell61 () (_ BitVec 4))
(declare-fun cell62 () (_ BitVec 4))
(declare-fun cell63 () (_ BitVec 4))
(declare-fun cell64 () (_ BitVec 4))
(declare-fun cell65 () (_ BitVec 4))
(declare-fun cell66 () (_ BitVec 4))
(declare-fun cell67 () (_ BitVec 4))
(declare-fun cell68 () (_ BitVec 4))

(declare-fun cell70 () (_ BitVec 4))
(declare-fun cell71 () (_ BitVec 4))
(declare-fun cell72 () (_ BitVec 4))
(declare-fun cell73 () (_ BitVec 4))
(declare-fun cell74 () (_ BitVec 4))
(declare-fun cell75 () (_ BitVec 4))
(declare-fun cell76 () (_ BitVec 4))
(declare-fun cell77 () (_ BitVec 4))
(declare-fun cell78 () (_ BitVec 4))

(declare-fun cell80 () (_ BitVec 4))
(declare-fun cell81 () (_ BitVec 4))
(declare-fun cell82 () (_ BitVec 4))
(declare-fun cell83 () (_ BitVec 4))
(declare-fun cell84 () (_ BitVec 4))
(declare-fun cell85 () (_ BitVec 4))
(declare-fun cell86 () (_ BitVec 4))
(declare-fun cell87 () (_ BitVec 4))
(declare-fun cell88 () (_ BitVec 4))

(assert (and (bvuge cell00 (_ bv1 4)) (bvule cell00 (_ bv9 4))))
(assert (and (bvuge cell01 (_ bv1 4)) (bvule cell01 (_ bv9 4))))
(assert (and (bvuge cell02 (_ bv1 4)) (bvule cell02 (_ bv9 4))))
(assert (and (bvuge cell03 (_ bv1 4)) (bvule cell03 (_ bv9 4))))
(assert (and (bvuge cell04 (_ bv1 4)) (bvule cell04 (_ bv9 4))))
(assert (and (bvuge cell05 (_ bv1 4)) (bvule cell05 (_ bv9 4))))
(assert (and (bvuge cell06 (_ bv1 4)) (bvule cell06 (_ bv9 4))))
(assert (and (bvuge cell07 (_ bv1 4)) (bvule cell07 (_ bv9 4))))
(assert (and (bvuge cell08 (_ bv1 4)) (bvule cell08 (_ bv9 4))))

(assert (and (bvuge cell10 (_ bv1 4)) (bvule cell10 (_ bv9 4))))
(assert (and (bvuge cell11 (_ bv1 4)) (bvule cell11 (_ bv9 4))))
(assert (and (bvuge cell12 (_ bv1 4)) (bvule cell12 (_ bv9 4))))
(assert (and (bvuge cell13 (_ bv1 4)) (bvule cell13 (_ bv9 4))))
(assert (and (bvuge cell14 (_ bv1 4)) (bvule cell14 (_ bv9 4))))
(assert (and (bvuge cell15 (_ bv1 4)) (bvule cell15 (_ bv9 4))))
(assert (and (bvuge cell16 (_ bv1 4)) (bvule cell16 (_ bv9 4))))
(assert (and (bvuge cell17 (_ bv1 4)) (bvule cell17 (_ bv9 4))))
(assert (and (bvuge cell18 (_ bv1 4)) (bvule cell18 (_ bv9 4))))

(assert (and (bvuge cell20 (_ bv1 4)) (bvule cell20 (_ bv9 4))))
(assert (and (bvuge cell21 (_ bv1 4)) (bvule cell21 (_ bv9 4))))
(assert (and (bvuge cell22 (_ bv1 4)) (bvule cell22 (_ bv9 4))))
(assert (and (bvuge cell23 (_ bv1 4)) (bvule cell23 (_ bv9 4))))
(assert (and (bvuge cell24 (_ bv1 4)) (bvule cell24 (_ bv9 4))))
(assert (and (bvuge cell25 (_ bv1 4)) (bvule cell25 (_ bv9 4))))
(assert (and (bvuge cell26 (_ bv1 4)) (bvule cell26 (_ bv9 4))))
(assert (and (bvuge cell27 (_ bv1 4)) (bvule cell27 (_ bv9 4))))
(assert (and (bvuge cell28 (_ bv1 4)) (bvule cell28 (_ bv9 4))))

(assert (and (bvuge cell30 (_ bv1 4)) (bvule cell30 (_ bv9 4))))
(assert (and (bvuge cell31 (_ bv1 4)) (bvule cell31 (_ bv9 4))))
(assert (and (bvuge cell32 (_ bv1 4)) (bvule cell32 (_ bv9 4))))
(assert (and (bvuge cell33 (_ bv1 4)) (bvule cell33 (_ bv9 4))))
(assert (and (bvuge cell34 (_ bv1 4)) (bvule cell34 (_ bv9 4))))
(assert (and (bvuge cell35 (_ bv1 4)) (bvule cell35 (_ bv9 4))))
(assert (and (bvuge cell36 (_ bv1 4)) (bvule cell36 (_ bv9 4))))
(assert (and (bvuge cell37 (_ bv1 4)) (bvule cell37 (_ bv9 4))))
(assert (and (bvuge cell38 (_ bv1 4)) (bvule cell38 (_ bv9 4))))

(assert (and (bvuge cell40 (_ bv1 4)) (bvule cell40 (_ bv9 4))))
(assert (and (bvuge cell41 (_ bv1 4)) (bvule cell41 (_ bv9 4))))
(assert (and (bvuge cell42 (_ bv1 4)) (bvule cell42 (_ bv9 4))))
(assert (and (bvuge cell43 (_ bv1 4)) (bvule cell43 (_ bv9 4))))
(assert (and (bvuge cell44 (_ bv1 4)) (bvule cell44 (_ bv9 4))))
(assert (and (bvuge cell45 (_ bv1 4)) (bvule cell45 (_ bv9 4))))
(assert (and (bvuge cell46 (_ bv1 4)) (bvule cell46 (_ bv9 4))))
(assert (and (bvuge cell47 (_ bv1 4)) (bvule cell47 (_ bv9 4))))
(assert (and (bvuge cell48 (_ bv1 4)) (bvule cell48 (_ bv9 4))))

(assert (and (bvuge cell50 (_ bv1 4)) (bvule cell50 (_ bv9 4))))
(assert (and (bvuge cell51 (_ bv1 4)) (bvule cell51 (_ bv9 4))))
(assert (and (bvuge cell52 (_ bv1 4)) (bvule cell52 (_ bv9 4))))
(assert (and (bvuge cell53 (_ bv1 4)) (bvule cell53 (_ bv9 4))))
(assert (and (bvuge cell54 (_ bv1 4)) (bvule cell54 (_ bv9 4))))
(assert (and (bvuge cell55 (_ bv1 4)) (bvule cell55 (_ bv9 4))))
(assert (and (bvuge cell56 (_ bv1 4)) (bvule cell56 (_ bv9 4))))
(assert (and (bvuge cell57 (_ bv1 4)) (bvule cell57 (_ bv9 4))))
(assert (and (bvuge cell58 (_ bv1 4)) (bvule cell58 (_ bv9 4))))

(assert (and (bvuge cell60 (_ bv1 4)) (bvule cell60 (_ bv9 4))))
(assert (and (bvuge cell61 (_ bv1 4)) (bvule cell61 (_ bv9 4))))
(assert (and (bvuge cell62 (_ bv1 4)) (bvule cell62 (_ bv9 4))))
(assert (and (bvuge cell63 (_ bv1 4)) (bvule cell63 (_ bv9 4))))
(assert (and (bvuge cell64 (_ bv1 4)) (bvule cell64 (_ bv9 4))))
(assert (and (bvuge cell65 (_ bv1 4)) (bvule cell65 (_ bv9 4))))
(assert (and (bvuge cell66 (_ bv1 4)) (bvule cell66 (_ bv9 4))))
(assert (and (bvuge cell67 (_ bv1 4)) (bvule cell67 (_ bv9 4))))
(assert (and (bvuge cell68 (_ bv1 4)) (bvule cell68 (_ bv9 4))))

(assert (and (bvuge cell70 (_ bv1 4)) (bvule cell70 (_ bv9 4))))
(assert (and (bvuge cell71 (_ bv1 4)) (bvule cell71 (_ bv9 4))))
(assert (and (bvuge cell72 (_ bv1 4)) (bvule cell72 (_ bv9 4))))
(assert (and (bvuge cell73 (_ bv1 4)) (bvule cell73 (_ bv9 4))))
(assert (and (bvuge cell74 (_ bv1 4)) (bvule cell74 (_ bv9 4))))
(assert (and (bvuge cell75 (_ bv1 4)) (bvule cell75 (_ bv9 4))))
(assert (and (bvuge cell76 (_ bv1 4)) (bvule cell76 (_ bv9 4))))
(assert (and (bvuge cell77 (_ bv1 4)) (bvule cell77 (_ bv9 4))))
(assert (and (bvuge cell78 (_ bv1 4)) (bvule cell78 (_ bv9 4))))

(assert (and (bvuge cell80 (_ bv1 4)) (bvule cell80 (_ bv9 4))))
(assert (and (bvuge cell81 (_ bv1 4)) (bvule cell81 (_ bv9 4))))
(assert (and (bvuge cell82 (_ bv1 4)) (bvule cell82 (_ bv9 4))))
(assert (and (bvuge cell83 (_ bv1 4)) (bvule cell83 (_ bv9 4))))
(assert (and (bvuge cell84 (_ bv1 4)) (bvule cell84 (_ bv9 4))))
(assert (and (bvuge cell85 (_ bv1 4)) (bvule cell85 (_ bv9 4))))
(assert (and (bvuge cell86 (_ bv1 4)) (bvule cell86 (_ bv9 4))))
(assert (and (bvuge cell87 (_ bv1 4)) (bvule cell87 (_ bv9 4))))
(assert (and (bvuge cell88 (_ bv1 4)) (bvule cell88 (_ bv9 4))))

(assert (distinct cell00 cell01 cell02 cell03 cell04 cell05 cell06 cell07 cell08))
(assert (distinct cell10 cell11 cell12 cell13 cell14 cell15 cell16 cell17 cell18))
(assert (distinct cell20 cell21 cell22 cell23 cell24 cell25 cell26 cell27 cell28))
(assert (distinct cell30 cell31 cell32 cell33 cell34 cell35 cell36 cell37 cell38))
(assert (distinct cell40 cell41 cell42 cell43 cell44 cell45 cell46 cell47 cell48))
(assert (distinct cell50 cell51 cell52 cell53 cell54 cell55 cell56 cell57 cell58))
(assert (distinct cell60 cell61 cell62 cell63 cell64 cell65 cell66 cell67 cell68))
(assert (distinct cell70 cell71 cell72 cell73 cell74 cell75 cell76 cell77 cell78))
(assert (distinct cell80 cell81 cell82 cell83 cell84 cell85 cell86 cell87 cell88))

(assert (distinct cell00 cell10 cell20 cell30 cell40 cell50 cell60 cell70 cell80))
(assert (distinct cell01 cell11 cell21 cell31 cell41 cell51 cell61 cell71 cell81))
(assert (distinct cell02 cell12 cell22 cell32 cell42 cell52 cell62 cell72 cell82))
(assert (distinct cell03 cell13 cell23 cell33 cell43 cell53 cell63 cell73 cell83))
(assert (distinct cell04 cell14 cell24 cell34 cell44 cell54 cell64 cell74 cell84))
(assert (distinct cell05 cell15 cell25 cell35 cell45 cell55 cell65 cell75 cell85))
(assert (distinct cell06 cell16 cell26 cell36 cell46 cell56 cell66 cell76 cell86))
(assert (distinct cell07 cell17 cell27 cell37 cell47 cell57 cell67 cell77 cell87))
(assert (distinct cell08 cell18 cell28 cell38 cell48 cell58 cell68 cell78 cell88))

(assert (distinct cell00 cell01 cell02 cell10 cell11 cell12 cell20 cell21 cell22))
(assert (distinct cell03 cell04 cell05 cell13 cell14 cell15 cell23 cell24 cell25))
(assert (distinct cell06 cell07 cell08 cell16 cell17 cell18 cell26 cell27 cell28))

(assert (distinct cell30 cell31 cell32 cell40 cell41 cell42 cell50 cell51 cell52))
(assert (distinct cell33 cell34 cell35 cell43 cell44 cell45 cell53 cell54 cell55))
(assert (distinct cell36 cell37 cell38 cell46 cell47 cell48 cell56 cell57 cell58))

(assert (distinct cell60 cell61 cell62 cell70 cell71 cell72 cell80 cell81 cell82))
(assert (distinct cell63 cell64 cell65 cell73 cell74 cell75 cell83 cell84 cell85))
(assert (distinct cell66 cell67 cell68 cell76 cell77 cell78 cell86 cell87 cell88))

; http://www.norvig.com/sudoku.html
; http://www.mirror.co.uk/news/weird-news/worlds-hardest-sudoku-can-you-242294

;------------------------------
;00 01 02 | 03 04 05 | 06 07 08
;10 11 12 | 13 14 15 | 16 17 18
;20 21 22 | 23 24 25 | 26 27 28
;------------------------------
;30 31 32 | 33 34 35 | 36 37 38
;40 41 42 | 43 44 45 | 46 47 48
;50 51 52 | 53 54 55 | 56 57 58
;------------------------------
;60 61 62 | 63 64 65 | 66 67 68
;70 71 72 | 73 74 75 | 76 77 78
;80 81 82 | 83 84 85 | 86 87 88
;------------------------------

;..53..... - 0
;8......2. - 1
;.7..1.5.. - 2
;4....53.. - 3
;.1..7...6 - 4
;..32...8. - 5
;.6.5....9 - 6
;..4....3. - 7
;.....97.. - 8

(assert (= cell02 #x5))
(assert (= cell03 #x3))
(assert (= cell10 #x8))
(assert (= cell17 #x2))
(assert (= cell21 #x7))
(assert (= cell24 #x1))
(assert (= cell26 #x5))
(assert (= cell30 #x4))
(assert (= cell35 #x5))
(assert (= cell36 #x3))
(assert (= cell41 #x1))
(assert (= cell44 #x7))
(assert (= cell48 #x6))
(assert (= cell52 #x3))
(assert (= cell53 #x2))
(assert (= cell57 #x8))
(assert (= cell61 #x6))
(assert (= cell63 #x5))
(assert (= cell68 #x9))
(assert (= cell72 #x4))
(assert (= cell77 #x3))
(assert (= cell84 #x9))
(assert (= cell86 #x7))

;(check-sat)
;(get-model)
(get-all-models)

