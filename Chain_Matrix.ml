(* ===============================================================*)
(*                                                                *)
(*            Formal Verification of Chain Matrix of              *)
(*                Coupled Transmission Lines                      *)
(*                            (Extension)                         *)
(*                                                                *)
(*                 (c) Copyright, Elif Deniz                      *)
(*                                                                *)
(*                   *Hardware Verification Group,                *)
(*         Department of Electrical and Computer Engineering      *)
(*                        Concordia University                    *) 
(*                        Montreal, Canada                        *)
(*                                                                *)
(*                                                                *)
(*                                                                *)
(*           Contact:   *<e_deniz@encs.concordia.ca>              *) 
(*                                                                *)
(*                                                                *)
(* ============================================================== *)


(*===================== Theories to load ==========================*)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/cvectors.ml";;
needs "Multivariate/cmatrix.ml";;


 let COMPLEX_CART_EQ = prove
  (`!x y:complex^N. x = y <=> !i. 1 <= i /\ i <= dimindex (:N) ==> x$i = y$i`,
  REWRITE_TAC[CART_EQ]);;


let CCOMMON_TAC xs =
  SIMP_TAC (xs @ [cmat2x2;cmatrix_cvector_mul;COMPLEX_CART_EQ;LAMBDA_BETA;
           CART_EQ;VECTOR_2;DIMINDEX_2;FORALL_2;DOT_2;VSUM_2]);;


let BMV_ADD_SIMP_TAC xs =
  SIMP_TAC (xs @ [bmatrix_bvector_mul;bm_sum;COMPLEX_CART_EQ;CART_EQ;LAMBDA_BETA;
  VECTOR_2;DIMINDEX_1;DIMINDEX_2;FORALL_1;FORALL_2;DOT_1;DOT_2;BM_SUM; VSUM_2;CMATRIX_ADD_COMPONENT]);;


(* ========================================================================= *)
(*                                                                           *)
(*                        2x2 BLOCK MATRICES                                 *)
(*                                                                           *)
(* ========================================================================= *)


make_overloadable "%" `:A-> B-> B`;;
 overload_interface("%",`(cvector_mul):complex->complex^N->complex^N`);;

let cvector_mul = new_definition

  `((%):complex->complex^N->complex^N) c x = lambda i. c * x$i`;;


make_overloadable "**" `:A->B->C`;;
make_overloadable "%%" `:A->B->B`;;


new_type_abbrev ("BMT",`:(complex^N^M)^N^M`);;

overload_interface ("+",`(bmatrix_add):BMT->BMT->BMT`);;
overload_interface ("-",`(bmatrix_sub):BMT->BMT->BMT`);;
overload_interface ("--",`(bmatrix_neg):BMT->BMT`);;
overload_interface ("**",`(bmatrix_mul):(complex^N^M)^N^M->(complex^P^N)^P^N->(complex^P^M)^P^M`);;
overload_interface ("%%",`bmatrix_smul:complex->BMT->BMT`);;



let bmatrix_add = new_definition
  `!A:BMT B:BMT. A + B = lambda i j. A$i$j + B$i$j`;;


let bmatrix_sub = new_definition
  `!A:BMT B:BMT. A - B = lambda i j. A$i$j - B$i$j`;;

let bmatrix_neg = new_definition
  `!A:BMT. --A = lambda i j. --(A$i$j)`;;

let bm_sum = new_definition
  `(bm_sum:(A->bool)->(A->complex^N^M)->complex^N^M) s f = lambda i j. vsum s (\x. f(x)$i$j)`;;

let bmatrix_mul = new_definition
  `!A:(complex^N^M)^N^M B:(complex^P^N)^P^N.
        A ** B =
          lambda i j. bm_sum(1..dimindex(:N)) (\k. A$i$k ** B$k$j)`;;

let bmatrix_smul = new_definition
  `((%%):complex->BMT->BMT) c (A:BMT) = lambda i j. c %% A$i$j`;;


let BMATRIX_ADD_COMPONENT = prove(
`!A B:BMT i j. (A + B)$i$j = A$i$j + B$i$j`,

 REPEAT GEN_TAC THEN
 SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:BMT. A$i = A$k` CHOOSE_TAC THENL
 [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
 SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:(complex^N^M)^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
   ASM_SIMP_TAC[bmatrix_add;LAMBDA_BETA]);;

let BMATRIX_SUB_COMPONENT = prove
 (`!A B:BMT i j. (A - B)$i$j = A$i$j - B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:BMT. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:(complex^N^M)^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[bmatrix_sub; LAMBDA_BETA]);;

let BMATRIX_NEG_COMPONENT = prove
 (`!A:BMT i j. (--A)$i$j = --(A$i$j)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:BMT. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:(complex^N^M)^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[bmatrix_neg; LAMBDA_BETA]);;

let BMATRIX_SMUL_COMPONENT = prove
 (`!c A:BMT i. (c %% A)$i$j = c %% A$i$j`,
  
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:BMT. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:(complex^N^M)^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cvector_mul;o_DEF;bmatrix_smul;vector_map; COMPLEX_CART_EQ; 
  LAMBDA_BETA]);;

let BM_SUM = prove
(`!A. bm_sum (1..2) A:(complex^N^N) = A(1) + A(2)`,
   CCOMMON_TAC[bm_sum;CMATRIX_ADD_COMPONENT]);;

let bmat2x2 = new_definition
  `bmat2x2 A B C D :(complex^2^2)^2^2 = vector[vector[A;B]; vector[C;D]]`;;

let BMATRIX_2x2 = prove
(`!(A:complex^2^2) B C D. (vector [vector [A; B] ; vector [C; D]]:(complex^2^2)^2^2)$1$1 = A /\
              (vector [vector [A; B] ; vector [C; D]]:(complex^2^2)^2^2)$1$2 = B /\
              (vector [vector [A; B] ; vector [C; D]]:(complex^2^2)^2^2)$2$1 = C /\
	      (vector [vector [A; B] ; vector [C; D]]:(complex^2^2)^2^2)$2$2 = D `,
         SIMP_TAC [vector; LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [ONE ;EL; TL; HD] THEN
         SIMP_TAC [LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [ONE ;EL; TL; HD]);;


(* ========================================================================= *)
(*                        Nx1 BLOCK VECTORS                                  *)
(* ========================================================================= *)


new_type_abbrev ("BVT",`:(complex^1^N)^N`);;

overload_interface ("+",`(bvector_add):BVT->BVT->BVT`);;
overload_interface ("-",`(bvector_sub):BVT->BVT->BVT`);;
overload_interface ("--",`(bvector_neg):BVT->BVT`);;
overload_interface ("**",`(bmatrix_bvector_mul):BMT->BVT->(complex^1^M)^M`);;
overload_interface ("%%",`colvector_lmul:complex->complex^1^N->complex^1^N`);;

let columnvector_Nx1 = new_definition
 `(columnvector_Nx1:complex^N->complex^1^N) v = lambda i j. v$i`;;


let rowvector_Nx1 = new_definition
 `(rowvector_Nx1:complex^N->complex^N^1) v = lambda i j. v$j`;;

let rowvector_2x1_new = new_definition
 `(rowvector_2x1_new:complex^2->complex^2^1) v = lambda i j. v$j`;;


let columnvector_2x1 = new_definition
 `(columnvector_2x1:complex^2->complex^1^2) v = lambda i j. v$i`;;

 let bvec2x1_new = new_definition
  `bvec2x1_new a1 a2 b1 b2 :(complex^1^2)^2  =
  vector[columnvector_2x1 (vector[a1 ;a2]:(complex^2)); columnvector_2x1(vector[b1 ;b2])]`;;

let bvec = new_definition
  `bvec (a1:complex->complex) a2 b1 b2 (z:complex) : (complex^1^2)^2 =
     vector[
       columnvector_2x1 (vector [a1 z; a2 z] : complex^2);
       columnvector_2x1 (vector [b1 z; b2 z])
     ]`;;


let bmatrix_bvector_mul = new_definition
  `!A:BMT x:BVT.
        A ** x = lambda i. bm_sum(1..dimindex(:N)) (\j. A$i$j ** x$j)`;;


let colvector_lmul = new_definition
  `((%%):complex->complex^1^N->complex^1^N) c (A:complex^1^N) = lambda i j. c * A$i$j`;;

let COLVEC_LMUL_COMPONENT = prove
 (`!c A:complex^1^N i. (c %% A)$i$j = c * A$i$j`,
  
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !A:complex^1^N. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:1) /\ !z:complex^1. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cvector_mul;o_DEF;cmatrix_smul;colvector_lmul;vector_map; COMPLEX_CART_EQ; 
  LAMBDA_BETA]);;

let bvector_add = new_definition
  `bvector_add (A:BVT) (B:BVT) = lambda j. A$j + B$j`;;



let BVECTOR_ADD_COMPONENT = prove(
`!A B:BVT i j. (A + B)$j = A$j + B$j`,

 REPEAT GEN_TAC THEN
 SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !A:BVT. A$i = A$k` CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
 SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:(complex^1^N)^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
   ASM_SIMP_TAC[bvector_add;LAMBDA_BETA]);;


let clvector_add = 
new_definition `clvector_add (A:(complex^1)^2) (B:(complex^1)^2) = (\j. A$j + B$j)`;;


let COLUMNVECTOR_2X1_ADD = prove
 (`columnvector_2x1 (vector [b1; b2]) + columnvector_2x1 (vector [c1; c2]) =
   columnvector_2x1 (vector [b1 + c1; b2 + c2])`,
  REWRITE_TAC [columnvector_2x1; bvector_add] THEN BMV_ADD_SIMP_TAC[bvector_add;BVECTOR_ADD_COMPONENT]);;


let COLUMNVECTOR_2X1_ADD_2 = prove
 (`columnvector_2x1 (vector [b1; b2]) + columnvector_2x1 (vector [c1; c2]) + columnvector_2x1 (vector [d1; d2]) + columnvector_2x1 (vector [e1; e2]) =
   columnvector_2x1 (vector [b1 + c1 + d1 + e1; b2 + c2 + d2 + e2])`,
  REWRITE_TAC [columnvector_2x1; bvector_add] THEN BMV_ADD_SIMP_TAC[bvector_add;BVECTOR_ADD_COMPONENT]);;



let COLUMNVECTOR_2X1_ADD_4 = prove
 (`columnvector_2x1 (vector [(b1:complex->complex) z; b2 z]) + columnvector_2x1 (vector [c1 z; c2 z]) + 
   columnvector_2x1 (vector [d1 z; d2 z]) + columnvector_2x1 (vector [e1 z; e2 z]) =
   columnvector_2x1 (vector [b1 z + c1 z + d1 z + e1 z; b2 z + c2 z + d2 z + e2 z])`,
  REWRITE_TAC [columnvector_2x1; bvector_add] THEN BMV_ADD_SIMP_TAC[bvector_add;BVECTOR_ADD_COMPONENT]);;



(* ------------------------------------------------------------------------- *)
(*                         Some Useful Theorems                              *)
(* ------------------------------------------------------------------------- *)

let BMATRIX_BVECTOR_MUL = prove (`!A B C D a1 a2 b1 b2. bmat2x2 A B C D ** bvec2x1_new a1 a2 b1 b2 = 
   vector[A ** columnvector_2x1 (vector[a1;a2]:(complex^2)) +
          B ** columnvector_2x1 (vector[b1;b2]) ;
	  C ** columnvector_2x1 (vector[a1;a2]) +
	  D ** columnvector_2x1 (vector[b1;b2])]`,

REWRITE_TAC[bmat2x2;bvec2x1_new] THEN
BMV_ADD_SIMP_TAC[]);;


let BMATRIX_MULT = prove
(`!A B C D P Q R S. bmat2x2 A B C D ** bmat2x2 P Q R S =
  bmat2x2 (A**P + B**R) (A**Q + B**S) (C**P + D**R) (C**Q + D**S)`,
  REWRITE_TAC[bmat2x2] THEN BMV_ADD_SIMP_TAC[bmatrix_mul]);;

let BMATRIX_SCALAR_LMUL = prove
  (`!(A:complex^2^2) B C D (k:complex). k %% bmat2x2 A B C D =
    bmat2x2 (k %% A) (k %% B) (k %% C) (k %% D)`,
     REWRITE_TAC[bmat2x2] THEN BMV_ADD_SIMP_TAC [bmatrix_smul;BMATRIX_SMUL_COMPONENT]);;

let BMATRIX_EQ = prove
  (`!A B C D P Q R S:complex^2^2. bmat2x2 A B C D = bmat2x2 P Q R S <=>
    A = P /\ B = Q /\ C = R /\ D = S`,
  REWRITE_TAC[bmat2x2] THEN BMV_ADD_SIMP_TAC [] THEN CONV_TAC TAUT);;

let BMAT_2X2_EQ_COMPONENT = prove(`
    !(M:(complex^2^2)^2^2). M = bmat2x2 (M$1$1) (M$1$2) (M$2$1) (M$2$2)`,
     REWRITE_TAC[bmat2x2] THEN BMV_ADD_SIMP_TAC[]);;

 let FORALL_BMATRIX_2X2 = prove
  (`!P. (!M:(complex^2^2)^2^2. P M) <=> ! A B C D.P (bmat2x2 A B C D )`,
 REWRITE_TAC[FORALL_VECTOR_2;bmat2x2] );;


let DOT_CROWVECTOR_CCOLUMNVECTOR = prove
 (`!A:complex^N^M v:complex^N. columnvector_Nx1(A ** v) = A ** columnvector_Nx1 v`,
  REWRITE_TAC[rowvector_Nx1; columnvector_Nx1; cmatrix_mul; cmatrix_cvector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA]);;


let DOT_CROWVECTOR_CCOLUMNVECTOR_2 = prove
 (`!A:complex^2^2 v:complex^2. columnvector_2x1(A ** v) = A ** columnvector_2x1 v`,
  REWRITE_TAC[rowvector_2x1_new; columnvector_2x1; cmatrix_mul; cmatrix_cvector_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA]);;


let CMAT2X2_VECTOR_MUL_ALT = prove
  (`!A B C D X Y:complex.
    vector [vector [A;B]; vector [C;D]]:complex^2^2 ** vector [X;Y] = vector[A*X+B*Y;C*X+D*Y]`,

CCOMMON_TAC[]);;

let COLVEC_EQ = prove(`!x y z t:complex.  columnvector_2x1 (vector [x;y] :complex^2) =
   columnvector_2x1 (vector [z;t]) <=>
      ((vector [x;y] :complex^2) = (vector [z;t]))`,

REWRITE_TAC[columnvector_2x1] THEN
CCOMMON_TAC[VECTOR_1;DIMINDEX_1;FORALL_1;DOT_1;VSUM_1]);;


let COLVEC2_EQ = prove (`!x y z t:complex.  columnvector_2x1 (vector [x;y] :complex^2) =
  columnvector_2x1 (vector [z;t]) <=> x = z /\ y = t`,

REPEAT STRIP_TAC THEN
REWRITE_TAC[COLVEC_EQ] THEN CCOMMON_TAC[CVECTOR2_EQ]);;

let CMATRIX_ADD_COMPONENT2 = prove
 (`!A B:complex^1^N i j. (A + B)$i$j = A$i$j + B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !A:complex^1^N. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:1) /\ !z:complex^1. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_add; LAMBDA_BETA]);;

let CVEC_COL_EQ = prove (`!a b c d x y k (t:complex->complex)(z:complex).
    (vector[columnvector_2x1 (vector [x z;y z]);
       columnvector_2x1 (vector [k z;t z]:complex^2):complex^1^2]:(complex^1^2)^2 =
	 vector[columnvector_2x1 (vector [a z;b z]);
	    columnvector_2x1 (vector[c z;d z])]) <=>
		(columnvector_2x1 (vector [x z; y z]) =  columnvector_2x1 (vector [a z; b z]) /\
		 columnvector_2x1 (vector [k z; t z]) = columnvector_2x1 (vector [c z; d z]))`,


REPEAT GEN_TAC THEN CCOMMON_TAC[CVECTOR2_EQ]);;

let CVEC_COL_EQ_ALTERNATIVE= prove (`!a b c d x y k (t:complex->complex)(z:complex).
    (bvec x y k t z):(complex^1^2)^2 =
	 (bvec a b c d z) <=>
			(columnvector_2x1 (vector [x z; y z]) =  columnvector_2x1 (vector [a z; b z]) /\
		 columnvector_2x1 (vector [k z; t z]) = columnvector_2x1 (vector [c z; d z]))`,

REPEAT GEN_TAC THEN CCOMMON_TAC[bvec;CVECTOR2_EQ]);;



(*===========================================================================*)
(*                       Chain Matrix Model of                               *)
(*                     Coupled Transmission Lines                            *)                                      
(*===========================================================================*)

let cmat2x2 = new_definition
  `cmat2x2 A B C D :complex^2^2 = vector[vector[A;B]; vector[C;D]]`;;


(*===================== Even-mode Matrix  =====================*)


let even_mat_def = new_definition
  `even_mat_def theta_e Z0e Y0e =
     cmat2x2 (Cx(cos theta_e)) (ii * Z0e * Cx(sin theta_e))
              (ii * Y0e * Cx(sin theta_e)) (Cx(cos theta_e))`;;


(*===================== Odd-mode Matrix  =====================*)

let odd_mat_def = new_definition
  `odd_mat_def theta_o Z0o Y0o =
     cmat2x2 (Cx(cos theta_o)) (ii * Z0o * Cx(sin theta_o))
              (ii * Y0o * Cx(sin theta_o)) (Cx(cos theta_o))`;;


(*===================== Even-mode Equation  =====================*)

let even_vol_left = new_definition
  `even_vol_left (V1:complex->complex) (V2:complex->complex) z = Cx(&1/ &2) * (V1 z + V2 z)`;;

let even_cur_left = new_definition
  `even_cur_left (II1:complex->complex) (II2:complex->complex) z = Cx(&1/ &2) * (II1 z + II2 z)`;;

let even_vol_right = new_definition
  `even_vol_right (V3:complex->complex) (V4:complex->complex) z = Cx(&1/ &2) * (V3 z + V4 z)`;;

let even_cur_right = new_definition
  `even_cur_right (II3:complex->complex) (II4:complex->complex) z = Cx(&1/ &2) * (II3 z + II4 z)`;;


let mode_clvec = new_definition
  `mode_clvec (vol:complex->complex) cur (z:complex) =
     (columnvector_2x1 ((vector [vol z; cur z]:complex^2)):complex^1^2)`;;

let even_send_vec = new_definition
  `even_send_vec V1 V2 II1 II2 z = mode_clvec (even_vol_left V1 V2) (even_cur_left II1 II2) z`;;

let even_recv_vec = new_definition
  `even_recv_vec V3 V4 II3 II4 z = mode_clvec (even_vol_right V3 V4) (even_cur_right II3 II4) z`;;


let even_mode_eq = new_definition
  `even_mode_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_e Z0e Y0e z <=>
    even_send_vec V1 V2 II1 II2 z = even_mat_def theta_e Z0e Y0e ** even_recv_vec V3 V4 II3 II4 z`;;


(*===================== Odd-mode Equation  =====================*)

let odd_vol_left = new_definition
  `odd_vol_left (V1:complex->complex) (V2:complex->complex) z = Cx(&1/ &2) * (V1 z - V2 z)`;;

let odd_cur_left = new_definition
  `odd_cur_left (II1:complex->complex) (II2:complex->complex) z = Cx(&1/ &2) * (II1 z - II2 z)`;;

let odd_vol_right = new_definition
  `odd_vol_right (V3:complex->complex) (V4:complex->complex) z = Cx(&1/ &2) * (V3 z - V4 z)`;;

let odd_cur_right = new_definition
  `odd_cur_right (II3:complex->complex) (II4:complex->complex) z = --Cx(&1/ &2) * (II3 z - II4 z)`;;

let odd_send_vec = new_definition
  `odd_send_vec V1 V2 II1 II2 z = mode_clvec (odd_vol_left V1 V2) (odd_cur_left II1 II2) z`;;

let odd_receive_vec = new_definition
  `odd_receive_vec V3 V4 II3 II4 z = mode_clvec (odd_vol_right V3 V4) (odd_cur_right II3 II4) z`;;


let odd_mode_eq = new_definition
  `odd_mode_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_o Z0o Y0o z <=>
    odd_send_vec V1 V2 II1 II2 z = odd_mat_def theta_o Z0o Y0o ** odd_receive_vec V3 V4 II3 II4 z`;;


(*======================================= SUBMATRIX ELEMENTS =====================================================*)

let a_11 = new_definition
  `a_11 theta_e theta_o = Cx(&1/ &2) * (Cx(cos theta_e) + Cx(cos theta_o))`;;


let a_12 = new_definition
  `a_12 theta_e theta_o = Cx(&1/ &2) * (Cx(cos theta_e) - Cx(cos theta_o))`;;

let a_21 = new_definition
  `a_21 theta_e theta_o = a_12 theta_e theta_o`;;

let a_22 = new_definition
  `a_22 theta_e theta_o = a_11 theta_e theta_o`;;


let c_11 = new_definition
  `c_11 theta_e theta_o Y0e Y0o = ii * Cx(&1/ &2) * (Y0e * Cx(sin theta_e) + Y0o * Cx(sin theta_o))`;;

let c_12 = new_definition
  `c_12 theta_e theta_o Y0e Y0o = ii * Cx(&1/ &2) * (Y0e * Cx(sin theta_e) - Y0o * Cx(sin theta_o))`;;

let c_21 = new_definition
  `c_21 theta_e theta_o Y0e Y0o = c_12 theta_e theta_o Y0e Y0o`;;

let c_22 = new_definition
  `c_22 theta_e theta_o Y0e Y0o = c_11 theta_e theta_o Y0e Y0o`;;


(*===================== Corrected Version of b abd c Elements  =====================*)

let nb_11 = new_definition
  `nb_11 theta_e theta_o Z0e Z0o = --ii * Cx(&1/ &2) * (Z0e * Cx(sin theta_e) - Z0o * Cx(sin theta_o))`;;

let nb_12 = new_definition
  `nb_12 theta_e theta_o Z0e Z0o = --ii * Cx(&1/ &2) * (Z0e * Cx(sin theta_e) + Z0o * Cx(sin theta_o))`;;
  
let nb_21 = new_definition
  `nb_21 theta_e theta_o Z0e Z0o = nb_12 theta_e theta_o Z0e Z0o`;;


let nb_22 = new_definition
  `nb_22 theta_e theta_o Z0e Z0o = nb_11 theta_e theta_o Z0e Z0o`;;

let nd_11 = new_definition
  `nd_11 theta_e theta_o = --Cx(&1/ &2) * (Cx(cos theta_e) - Cx(cos theta_o))`;;

let nd_12 = new_definition
  `nd_12 theta_e theta_o = --Cx(&1/ &2) * (Cx(cos theta_e) + Cx(cos theta_o))`;;

let nd_21 = new_definition
  `nd_21 theta_e theta_o = nd_12 theta_e theta_o`;;

let nd_22 = new_definition
  `nd_22 theta_e theta_o = nd_11 theta_e theta_o`;;



(*============================ Definition of 2x2 Submatrices as vector of vectors ==============================*)

let matA_sub = new_definition
  `matA_sub theta_e theta_o = (vector [
    vector [a_11 theta_e theta_o; a_12 theta_e theta_o];
    vector [a_21 theta_e theta_o; a_22 theta_e theta_o]]:complex^2^2)`;;

let nmatB_sub = new_definition
  `nmatB_sub theta_e theta_o Z0e Z0o = (vector[
    vector [nb_11 theta_e theta_o Z0e Z0o; nb_12 theta_e theta_o Z0e Z0o];
    vector [nb_21 theta_e theta_o Z0e Z0o; nb_22 theta_e theta_o Z0e Z0o]]:complex^2^2)`;;

let matC_sub = new_definition
  `matC_sub theta_e theta_o Y0e Y0o = (vector[
    vector [c_11 theta_e theta_o Y0e Y0o; c_12 theta_e theta_o Y0e Y0o];
    vector [c_21 theta_e theta_o Y0e Y0o; c_22 theta_e theta_o Y0e Y0o]]:complex^2^2)`;;

let nmatD_sub = new_definition
  `nmatD_sub theta_e theta_o = (vector [
    vector [nd_11 theta_e theta_o; nd_12 theta_e theta_o];
    vector [nd_21 theta_e theta_o; nd_22 theta_e theta_o]]:complex^2^2)`;;
  


(*============================ Definition of left 4x1 Vector ==========================================*)


let chain_left_vec = new_definition
  `chain_left_vec (V1:complex->complex) V2 II1 II2 z = vector[columnvector_2x1 (vector [V1 z; V2 z]:complex^2);
                                                columnvector_2x1 (vector [II1 z; II2 z]):complex^1^2]`;;

let chain_left_vector = new_definition
  `chain_left_vector (V1:complex->complex) (V2:complex->complex) 
        (II1:complex->complex) (II2:complex->complex) z =
                                       bvec V1 V2 II1 II2 z`;;


(*============================   Definition of Right 4x1 Vector  ========================================== *)

let chain_right_vector = new_definition
  `chain_right_vector (V3:complex->complex) (V4:complex->complex) (II3:complex->complex) (II4:complex->complex) z =
   bvec V3 V4 (\z. --(II3 z)) (\z. --(II4 z)) z`;;

(* ================ Definition of Full 4x4 Chain Matrix by Combining Submatrices ========================*)

let nchain_block = new_definition `
  nchain_block theta_e theta_o Z0e Z0o Y0e Y0o =
    (bmat2x2 (matA_sub theta_e theta_o) (nmatB_sub theta_e theta_o Z0e Z0o)
     (matC_sub theta_e theta_o Y0e Y0o) 
          (nmatD_sub theta_e theta_o)):(complex^2^2)^2^2`;;


let chain_matrix_eq = new_definition
  `chain_matrix_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_e theta_o Z0e Z0o Y0e Y0o z <=>
    chain_left_vector V1 V2 II1 II2 z = nchain_block theta_e theta_o Z0e Z0o Y0e Y0o **
             chain_right_vector V3 V4 II3 II4 z`;;


(*================= Theorem: Prove the chain equation ============================ *)

g `!V1 V2 II1 II2 V3 V4 II3 II4 theta_e theta_o Z0e Z0o Y0e Y0o z.
     even_mode_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_e Z0e Y0e z /\
      odd_mode_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_o Z0o Y0o z
      <=> chain_matrix_eq V1 V2 II1 II2 V3 V4 II3 II4 theta_e theta_o Z0e Z0o Y0e Y0o z`;;
      
 e (REPEAT GEN_TAC);;
 e (REWRITE_TAC[even_mode_eq; odd_mode_eq;chain_matrix_eq]);;
 
 e (REWRITE_TAC[even_send_vec;even_mat_def;even_recv_vec;odd_send_vec;odd_mat_def;odd_receive_vec;chain_left_vector;nchain_block;chain_right_vector]);;
 
e (REWRITE_TAC[mode_clvec;even_vol_left;even_cur_left;even_vol_right;even_cur_right;odd_vol_left;odd_cur_left;cmat2x2;odd_vol_right;odd_cur_right;bmat2x2;bvec]);;

e (SUBGOAL_THEN `(vector
 [vector [Cx (cos theta_e); ii * Z0e * Cx (sin theta_e)];
  vector [ii * Y0e * Cx (sin theta_e); Cx (cos theta_e)]]):complex^2^2 **
 columnvector_2x1
 (vector [Cx (&1 / &2) * ((V3:complex->complex) (z:complex) + V4 z); Cx (&1 / &2) * ((II3:complex->complex) (z:complex) + II4 z)]:complex^2):complex^1^2 = columnvector_2x1
 (vector
  [Cx (cos theta_e) * Cx (&1 / &2) * (V3 z + V4 z) +
   ii * Z0e * Cx (sin theta_e) * Cx (&1 / &2) * (II3 z + II4 z);
   ii * Y0e * Cx (sin theta_e) * Cx (&1 / &2) * (V3 z + V4 z) +
   Cx (cos theta_e) * Cx (&1 / &2) * (II3 z + II4 z)])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (BMV_ADD_SIMP_TAC[]);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (AP_THM_TAC);;
e (AP_TERM_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (ONCE_ASM_REWRITE_TAC[]);;


e (SUBGOAL_THEN
  `vector
     [vector [Cx (cos theta_o); ii * Z0o * Cx (sin theta_o)] : complex^2;
      vector [ii * Y0o * Cx (sin theta_o); Cx (cos theta_o)]] **
   columnvector_2x1
     (vector [Cx (&1 / &2) * ((V3:complex->complex) (z:complex) - V4 z);
             --Cx (&1 / &2) * (II3 z - II4 z)]) : complex^1^2 =
   columnvector_2x1
     (vector
       [Cx (cos theta_o) * Cx (&1 / &2) * (V3 z - V4 z) +
        ii * Z0o * Cx (sin theta_o) * --Cx (&1 / &2) * (II3 z - II4 z);
        ii * Y0o * Cx (sin theta_o) * Cx (&1 / &2) * (V3 z - V4 z) +
        Cx (cos theta_o) * --Cx (&1 / &2) * (II3 z - II4 z)])`
  ASSUME_TAC);;


e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_SUB_COMPONENT;CMATRIX_ADD_COMPONENT2]);;
e (BMV_ADD_SIMP_TAC[]);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (AP_THM_TAC);;
e (AP_TERM_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (STRIP_TAC);;
e (BMV_ADD_SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (BINOP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMP_TAC[]);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (POP_ASSUM_LIST (K ALL_TAC));;
e(SIMP_TAC[COLVEC2_EQ]);;
e (EQ_TAC);;
e (ASSERT_TAC `(Cx (&1 / &2) * (V1 z + V2 z) =
  Cx (cos theta_e) * Cx (&1 / &2) * ((V3:complex->complex) z + V4 z) +
  ii * Z0e * Cx (sin theta_e) * Cx (&1 / &2) * (II3 z + II4 z)) <=> ((V1 z + V2 z) =
  Cx (cos theta_e) *  (V3 z + V4 z) +
  ii * Z0e * Cx (sin theta_e) * (II3 z + II4 z))`);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;

e (ASSERT_TAC `(Cx (&1 / &2) * ((II1:complex->complex) z + II2 z) =
  ii * Y0e * Cx (sin theta_e) * Cx (&1 / &2) * (V3 z + V4 z) +
  Cx (cos theta_e) * Cx (&1 / &2) * (II3 z + II4 z)) <=>  ((II1 z + II2 z) =
  ii * Y0e * Cx (sin theta_e) * (V3 z + V4 z) +
  Cx (cos theta_e) * (II3 z + II4 z))`);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;

 e (ASSERT_TAC `(Cx (&1 / &2) * ((V1:complex->complex) z - V2 z) =
 Cx (cos theta_o) * Cx (&1 / &2) * (V3 z - V4 z) +
 ii * Z0o * Cx (sin theta_o) * --Cx (&1 / &2) * (II3 z - II4 z) /\
 Cx (&1 / &2) * (II1 z - II2 z) =
 ii * Y0o * Cx (sin theta_o) * Cx (&1 / &2) * (V3 z - V4 z) +
 Cx (cos theta_o) * --Cx (&1 / &2) * (II3 z - II4 z)) <=> ((V1 z - V2 z) =
 Cx (cos theta_o) * (V3 z - V4 z) -
 ii * Z0o * Cx (sin theta_o) * (II3 z - II4 z) /\
 (II1 z - II2 z) =
 ii * Y0o * Cx (sin theta_o) *  (V3 z - V4 z) -
 Cx (cos theta_o) * (II3 z - II4 z))`);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;

e (POP_ASSUM_LIST (K ALL_TAC));;

e (REPEAT STRIP_TAC);;

 e (ASSERT_TAC `((V1:complex->complex) z + V2 z) + (V1 z - V2 z) =
   Cx (cos theta_e) * (V3 z + V4 z) +
  ii * Z0e * Cx (sin theta_e) * (II3 z + II4 z) +
   (Cx (cos theta_o) * (V3 z - V4 z) -
 ii * Z0o * Cx (sin theta_o) * (II3 z - II4 z))`);;

e (ASM_SIMP_TAC[]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(Cx (&2) * (V1:complex->complex) z = Cx (cos theta_e) * (V3 z + V4 z) +
ii * Z0e * Cx (sin theta_e) * (II3 z + II4 z) +
Cx (cos theta_o) * (V3 z - V4 z) -
ii * Z0o * Cx (sin theta_o) * (II3 z - II4 z))` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(V1:complex->complex) z = (Cx (&1) / Cx (&2)) * (Cx (cos theta_e) + Cx (cos theta_o)) * V3 z + 
                  (Cx (&1) / Cx (&2)) * (Cx (cos theta_e) - Cx (cos theta_o)) * V4 z + 
                  (ii / Cx (&2)) * (Z0e * Cx (sin theta_e) - Z0o * Cx (sin theta_o)) * II3 z + 
                  (ii / Cx (&2)) * (Z0e * Cx (sin theta_e) + Z0o * Cx (sin theta_o)) * II4 z` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ASSERT_TAC `((V1:complex->complex) z + V2 z) - (V1 z - V2 z) =
   Cx (cos theta_e) * (V3 z + V4 z) + ii * Z0e * Cx (sin theta_e) * (II3 z + II4 z) -
   Cx (cos theta_o) * (V3 z - V4 z) + ii * Z0o * Cx (sin theta_o) * (II3 z - II4 z)`);;

e (ASM_SIMP_TAC[]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(Cx (&2) * (V2:complex->complex) z = Cx (cos theta_e) * (V3 z + V4 z) +
ii * Z0e * Cx (sin theta_e) * (II3 z + II4 z) -
Cx (cos theta_o) * (V3 z - V4 z) +
ii * Z0o * Cx (sin theta_o) * (II3 z - II4 z))` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(V2:complex->complex) z = (Cx (&1) / Cx (&2)) * (Cx (cos theta_e) - Cx (cos theta_o)) * V3 z + 
                  (Cx (&1) / Cx (&2)) * (Cx (cos theta_e) + Cx (cos theta_o)) * V4 z + 
                  (ii / Cx (&2)) * (Z0e * Cx (sin theta_e) + Z0o * Cx (sin theta_o)) * II3 z + 
                  (ii / Cx (&2)) * (Z0e * Cx (sin theta_e) - Z0o * Cx (sin theta_o)) * II4 z` ASSUME_TAC);;


e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ASSERT_TAC `((II1:complex->complex) z + II2 z) + (II1 z - II2 z) =
  ii * Y0e * Cx (sin theta_e) * (V3 z + V4 z) +
      Cx (cos theta_e) * (II3 z + II4 z) +  ii * Y0o * Cx (sin theta_o) * (V3 z - V4 z) -
      Cx (cos theta_o) * (II3 z - II4 z)`);;


e (ASM_SIMP_TAC[]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(Cx (&2) * (II1:complex->complex) z = ii * Y0e * Cx (sin theta_e) * (V3 z + V4 z) +
Cx (cos theta_e) * (II3 z + II4 z) + ii * Y0o * Cx (sin theta_o) * (V3 z - V4 z) -
Cx (cos theta_o) * (II3 z - II4 z))` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(II1:complex->complex) z = (ii / Cx (&2)) * (Y0e * Cx (sin theta_e) +
Y0o * Cx (sin theta_o)) * V3 z + (ii / Cx (&2)) * (Y0e * Cx (sin theta_e) - Y0o * Cx (sin theta_o)) * V4 z +
Cx (&1) / Cx (&2) * (Cx (cos theta_e) - Cx (cos theta_o)) * II3 z + Cx (&1) / Cx (&2) * (Cx (cos theta_e) +
Cx (cos theta_o)) * (II4:complex->complex) z` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (ASSERT_TAC `((II1:complex->complex) z + II2 z) - (II1 z - II2 z) =
  ii * Y0e * Cx (sin theta_e) * (V3 z + V4 z) +
      Cx (cos theta_e) * (II3 z + II4 z) -  (ii * Y0o * Cx (sin theta_o) * (V3 z - V4 z) -
      Cx (cos theta_o) * (II3 z - II4 z))`);;

e (ASM_SIMP_TAC[]);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(Cx (&2) * (II2:complex->complex) z = ii * Y0e * Cx (sin theta_e) * (V3 z + V4 z) +
Cx (cos theta_e) * (II3 z + II4 z) - ii * Y0o * Cx (sin theta_o) * (V3 z - V4 z) +
Cx (cos theta_o) * (II3 z - II4 z))` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN `(II2:complex->complex) z = (ii / Cx (&2)) * (Y0e * Cx (sin theta_e) - Y0o * Cx (sin theta_o)) * V3 z +
(ii / Cx (&2)) * (Y0e * Cx (sin theta_e) + Y0o * Cx (sin theta_o)) * V4 z + Cx (&1) / Cx (&2) * (Cx (cos theta_e) + Cx (cos theta_o)) * II3 z + 
Cx (&1) / Cx (&2) * (Cx (cos theta_e) - Cx (cos theta_o)) * II4 z` ASSUME_TAC);;

e (POP_ASSUM MP_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;

e (SUBGOAL_THEN
  `vector
     [vector [matA_sub theta_e theta_o; nmatB_sub theta_e theta_o Z0e Z0o];
      vector [matC_sub theta_e theta_o Y0e Y0o; nmatD_sub theta_e theta_o]] **
   vector
     [columnvector_2x1 (vector [V3 z; V4 z]);
      columnvector_2x1 (vector [--II3 z; --II4 z] :complex^2)] =
   vector
     [matA_sub theta_e theta_o ** columnvector_2x1 (vector [(V3:complex->complex) z; V4 z]) +
      nmatB_sub theta_e theta_o Z0e Z0o ** columnvector_2x1 (vector [--II3 z; --II4 z]);
      matC_sub theta_e theta_o Y0e Y0o ** columnvector_2x1 (vector [V3 z; V4 z]) +
      nmatD_sub theta_e theta_o ** columnvector_2x1 (vector [--II3 z; --II4 z])]`
  ASSUME_TAC);;

e (BMV_ADD_SIMP_TAC[]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC[matA_sub;nmatB_sub;matC_sub;nmatD_sub]);;

e (SUBGOAL_THEN
  `vector
   [vector [a_11 theta_e theta_o; a_12 theta_e theta_o];
    vector [a_21 theta_e theta_o; a_22 theta_e theta_o]]:complex^2^2 **
   columnvector_2x1 (vector [V3 z; V4 z]):(complex^1)^2 =
   columnvector_2x1 (vector
     [a_11 theta_e theta_o * (V3:complex->complex) z + a_12 theta_e theta_o * V4 z;
      a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z])`
  ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;

e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;

e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [nb_11 theta_e theta_o Z0e Z0o; nb_12 theta_e theta_o Z0e Z0o];
   vector [nb_21 theta_e theta_o Z0e Z0o; nb_22 theta_e theta_o Z0e Z0o]]:complex^2^2 **
  columnvector_2x1 (vector [--II3 z; --II4 z]):complex^1^2 =  columnvector_2x1 (vector [nb_11 theta_e theta_o Z0e Z0o * 
  --((II3:complex->complex) z) + nb_12 theta_e theta_o Z0e Z0o * --(II4 z) ; nb_21 theta_e theta_o Z0e Z0o * --(II3 z) +
  nb_22 theta_e theta_o Z0e Z0o * --(II4 z)])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [c_11 theta_e theta_o Y0e Y0o; c_12 theta_e theta_o Y0e Y0o];
   vector [c_21 theta_e theta_o Y0e Y0o; c_22 theta_e theta_o Y0e Y0o]]:complex^2^2 **
  columnvector_2x1 (vector [(V3:complex->complex) z; V4 z]):(complex^1)^2 =
   columnvector_2x1 (vector [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z; 
    c_21 theta_e theta_o Y0e Y0o * V3 z + c_22 theta_e theta_o Y0e Y0o * V4 z])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [nd_11 theta_e theta_o; nd_12 theta_e theta_o];
   vector [nd_21 theta_e theta_o; nd_22 theta_e theta_o]]:complex^2^2 **
  columnvector_2x1 (vector [--(II3:complex->complex) z; --II4 z]):complex^1^2 =
   columnvector_2x1 (vector [nd_11 theta_e theta_o * --II3 z + nd_12 theta_e theta_o * --II4 z ;
    nd_21 theta_e theta_o * --II3 z + nd_22 theta_e theta_o * --II4 z])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN
  `(vector
    [(columnvector_2x1
        (vector
          [a_11 theta_e theta_o * (V3:complex->complex) z + a_12 theta_e theta_o * V4 z;
           a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z])) +
     columnvector_2x1
        (vector
          [nb_11 theta_e theta_o Z0e Z0o * --((II3:complex->complex) z) + nb_12 theta_e theta_o Z0e Z0o * --(II4 z);
           nb_21 theta_e theta_o Z0e Z0o * --(II3 z) + nb_22 theta_e theta_o Z0e Z0o * --(II4 z)]);

     (columnvector_2x1
        (vector
          [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z;
           c_21 theta_e theta_o Y0e Y0o * V3 z + c_22 theta_e theta_o Y0e Y0o * V4 z])) +
     columnvector_2x1
        (vector
          [nd_11 theta_e theta_o * --(II3 z) + nd_12 theta_e theta_o * --(II4 z);
           nd_21 theta_e theta_o * --(II3 z) + nd_22 theta_e theta_o * --(II4 z)])])
   =
   (vector
    [columnvector_2x1
       (vector
         [a_11 theta_e theta_o * V3 z + a_12 theta_e theta_o * V4 z +
          nb_11 theta_e theta_o Z0e Z0o * --(II3 z) +
          nb_12 theta_e theta_o Z0e Z0o * --(II4 z);
          a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z +
          nb_21 theta_e theta_o Z0e Z0o * --(II3 z) +
          nb_22 theta_e theta_o Z0e Z0o * --(II4 z)]) ;

    columnvector_2x1
       (vector
         [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z +
          nd_11 theta_e theta_o * --(II3 z) +
          nd_12 theta_e theta_o * --(II4 z);
          c_21 theta_e theta_o Y0e Y0o * V3 z + c_22 theta_e theta_o Y0e Y0o * V4 z +
          nd_21 theta_e theta_o * --(II3 z) +
          nd_22 theta_e theta_o * --(II4 z)])] :(complex^1^2^2))`

ASSUME_TAC);;

e (BMV_ADD_SIMP_TAC[bvector_add;BVECTOR_ADD_COMPONENT;COLUMNVECTOR_2X1_ADD;COLUMNVECTOR_2X1_ADD_2;COLUMNVECTOR_2X1_ADD_4;COMPLEX_ADD_AC ]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;
e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[a_11;a_12;a_21;a_22;nb_11;nb_12;nb_21;nb_22;c_11;c_12;c_21;c_22;nd_11;nd_12;nd_21;nd_22]);;
e (SIMP_TAC[CVEC_COL_EQ;COLVEC_EQ;CVECTOR2_EQ]);;
e (CONV_TAC COMPLEX_FIELD);;

e (SUBGOAL_THEN
  `vector
     [vector [matA_sub theta_e theta_o; nmatB_sub theta_e theta_o Z0e Z0o];
      vector [matC_sub theta_e theta_o Y0e Y0o; nmatD_sub theta_e theta_o]] **
   vector
     [columnvector_2x1 (vector [V3 z; V4 z]);
      columnvector_2x1 (vector [--II3 z; --II4 z] :complex^2)] =
   vector
     [matA_sub theta_e theta_o ** columnvector_2x1 (vector [(V3:complex->complex) z; V4 z]) +
      nmatB_sub theta_e theta_o Z0e Z0o ** columnvector_2x1 (vector [--II3 z; --II4 z]);
      matC_sub theta_e theta_o Y0e Y0o ** columnvector_2x1 (vector [V3 z; V4 z]) +
      nmatD_sub theta_e theta_o ** columnvector_2x1 (vector [--II3 z; --II4 z])]`
  ASSUME_TAC);;

e (BMV_ADD_SIMP_TAC[]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC[matA_sub;nmatB_sub;matC_sub;nmatD_sub]);;

e (SUBGOAL_THEN
  `vector
   [vector [a_11 theta_e theta_o; a_12 theta_e theta_o];
    vector [a_21 theta_e theta_o; a_22 theta_e theta_o]]:complex^2^2 **
   columnvector_2x1 (vector [V3 z; V4 z]):(complex^1)^2 =
   columnvector_2x1 (vector
     [a_11 theta_e theta_o * (V3:complex->complex) z + a_12 theta_e theta_o * V4 z;
      a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z])`
  ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [nb_11 theta_e theta_o Z0e Z0o; nb_12 theta_e theta_o Z0e Z0o];
   vector [nb_21 theta_e theta_o Z0e Z0o; nb_22 theta_e theta_o Z0e Z0o]]:complex^2^2 **
  columnvector_2x1 (vector [--II3 z; --II4 z]):complex^1^2 =  
   columnvector_2x1 (vector [nb_11 theta_e theta_o Z0e Z0o * --((II3:complex->complex) z) + nb_12 theta_e theta_o Z0e Z0o * 
    --(II4 z) ; nb_21 theta_e theta_o Z0e Z0o * --(II3 z) + nb_22 theta_e theta_o Z0e Z0o * --(II4 z)])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [c_11 theta_e theta_o Y0e Y0o; c_12 theta_e theta_o Y0e Y0o];
   vector [c_21 theta_e theta_o Y0e Y0o; c_22 theta_e theta_o Y0e Y0o]]:complex^2^2 **
  columnvector_2x1 (vector [(V3:complex->complex) z; V4 z]):(complex^1)^2 =
   columnvector_2x1 (vector [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z; c_21 theta_e theta_o Y0e Y0o * V3 z + 
    c_22 theta_e theta_o Y0e Y0o * V4 z])` ASSUME_TAC);;

e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN `vector
  [vector [nd_11 theta_e theta_o; nd_12 theta_e theta_o];
   vector [nd_21 theta_e theta_o; nd_22 theta_e theta_o]]:complex^2^2 **
  columnvector_2x1 (vector [--(II3:complex->complex) z; --II4 z]):complex^1^2 = 
   columnvector_2x1 (vector [nd_11 theta_e theta_o * --II3 z + nd_12 theta_e theta_o * --II4 z ; nd_21 theta_e theta_o * 
    --II3 z + nd_22 theta_e theta_o * --II4 z])` ASSUME_TAC);;


e (REWRITE_TAC[GSYM DOT_CROWVECTOR_CCOLUMNVECTOR_2]);;
e (REWRITE_TAC[columnvector_2x1] THEN CCOMMON_TAC[CMATRIX_ADD_COMPONENT2]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;

e (SUBGOAL_THEN
  `(vector
    [(columnvector_2x1
        (vector
          [a_11 theta_e theta_o * (V3:complex->complex) z + a_12 theta_e theta_o * V4 z;
           a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z])) +
     columnvector_2x1
        (vector
          [nb_11 theta_e theta_o Z0e Z0o * --((II3:complex->complex) z) + nb_12 theta_e theta_o Z0e Z0o * --(II4 z);
           nb_21 theta_e theta_o Z0e Z0o * --(II3 z) + nb_22 theta_e theta_o Z0e Z0o * --(II4 z)]);

     (columnvector_2x1
        (vector
          [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z;
           c_21 theta_e theta_o Y0e Y0o * V3 z + c_22 theta_e theta_o Y0e Y0o * V4 z])) +
     columnvector_2x1
        (vector
          [nd_11 theta_e theta_o * --(II3 z) + nd_12 theta_e theta_o * --(II4 z);
           nd_21 theta_e theta_o * --(II3 z) + nd_22 theta_e theta_o * --(II4 z)])])
   =
   (vector
    [columnvector_2x1
       (vector
         [a_11 theta_e theta_o * V3 z + a_12 theta_e theta_o * V4 z +
          nb_11 theta_e theta_o Z0e Z0o * --(II3 z) +
          nb_12 theta_e theta_o Z0e Z0o * --(II4 z);
          a_21 theta_e theta_o * V3 z + a_22 theta_e theta_o * V4 z +
          nb_21 theta_e theta_o Z0e Z0o * --(II3 z) +
          nb_22 theta_e theta_o Z0e Z0o * --(II4 z)]) ;

    columnvector_2x1
       (vector
         [c_11 theta_e theta_o Y0e Y0o * V3 z + c_12 theta_e theta_o Y0e Y0o * V4 z +
          nd_11 theta_e theta_o * --(II3 z) +
          nd_12 theta_e theta_o * --(II4 z);
          c_21 theta_e theta_o Y0e Y0o * V3 z + c_22 theta_e theta_o Y0e Y0o * V4 z +
          nd_21 theta_e theta_o * --(II3 z) +
          nd_22 theta_e theta_o * --(II4 z)])] :(complex^1^2^2))`

ASSUME_TAC);;

e (BMV_ADD_SIMP_TAC[bvector_add;BVECTOR_ADD_COMPONENT;COLUMNVECTOR_2X1_ADD;COLUMNVECTOR_2X1_ADD_2;
COLUMNVECTOR_2X1_ADD_4;COMPLEX_ADD_AC ]);;
e (FIRST_X_ASSUM (fun th -> REWRITE_TAC [th]));;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[a_11;a_12;a_21;a_22;nb_11;nb_12;nb_21;nb_22;c_11;c_12;c_21;c_22;nd_11;nd_12;nd_21;nd_22]);;
e (SIMP_TAC[CVEC_COL_EQ;COLVEC_EQ;CVECTOR2_EQ]);;

e (CONV_TAC COMPLEX_FIELD);;

(*=================================================================*)
(*                  End of the Formalization                       *)
(*=================================================================*)








