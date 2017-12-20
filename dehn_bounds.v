Require Import Reals.
Require Import Interval.Interval_tactic.
Require Import Coquelicot.Coquelicot.

Open Scope R_scope.

(* The following are from Definition 12 
   from section 2 of the paper. *)

Definition asinh x := ln (x + sqrt (x^2 + 1)).

Definition S := (1/(2 * sqrt 2)) / asinh (1/(2 * sqrt 2)).

Definition K := 2 * (sqrt 3) / S.

Definition h z  := (1 + z^2) / (z * (1 - z^2)).

Definition gU z := (1 + z^2) / (2 * (z ^ 3)).

Definition gL z := (1 + z^2)^2 / (2 * z^3 * (3 - z^2)).

Definition H z := (h z) / K.

Definition GU z := (gU z) / K.

Definition GL z := (gL z) / K.

Notation "x ^ y" := (powerRZ x y).

(* At this point we just copy in things from Maxima,
   using Maxima's grind command.
*)
Definition FU z := -(z^4+6*z^2+4*z+1)/((z+1)*(z^2+1)^2).
Definition FL z := -(z^6+7*z^4+12*z^3-9*z^2-4*z+1)/((z+1)*(z^2+1)*(z^2-2*z-1)*(z^2+2*z-1)).

Definition PHU z := RInt FU 1 z.
Definition fU z := K * (1 - z) * exp (- PHU z).

Definition PHL z := RInt FL 1 z.
Definition fL z := K * (1 - z) * exp (- PHL z).

Definition LB_igd w :=
  2^(7/2)*sqrt(3)*asinh(1/2^(3/2))*w^2*(w^2-3)*(w^4+4*w^2-1)
                                                 /((w^2+1)^2*(w^2-2*w-1)*(w^2+2*w-1)).
Definition LB z := (1/4) * RInt LB_igd z 1.

Definition UB_igd w :=
  2^(7/2)*sqrt(3)*asinh(1/2^(3/2))*w^2*(w^4+4*w^2-1)/(w^2+1)^3.
Definition UB z := (1/4) * RInt UB_igd z 1.

Lemma fU_concavity:
  forall z, 811/1000 <= z <= 1 ->
            -2*(z^8+6*z^6+32*z^4+10*z^2-1)/((z+1)*(z^2+1)^4) < 0.
Proof.
  intros. interval with (i_bisect_diff z).
Qed.

Lemma fL_concavity:
  forall z, 811/1000 <= z <= 1 -> 
  -2*(z^12-4*z^10+17*z^8-248*z^6+203*z^4-36*z^2+3)
       /((z+1)*(z^2+1)^2*(z^2-2*z-1)^2*(z^2+2*z-1)^2) > 0.
Proof.
  intros. interval with (i_bisect_diff z).
Qed.

Lemma LB_concavity:
  forall z,
    811/1000 <= z <= 1 ->
    (5*z^8-6*z^6+88*z^4-26*z^2+3) > 0.
Proof.
  intros. interval with (i_bisect_diff z).
Qed.

Lemma UB_concavity:
  forall z,
    811/1000 <= z <= 1 ->
    z^4-10*z^2+1 < 0.
Proof.
  intros. interval with (i_bisect_diff z).
Qed.

(* The above lemmata prove something slightly stronger
   than Lemma 25, namely that the consequents of Lemma
   25 hold when z is in [0.811,1]. We now prove xi > 0.811. *)

(* The following long expression is grind(-factor(expand(FL + 1/(1-z)))). 
   It has the same sign as the derivative of fL. *)

Lemma fL_decreasing:
  forall z,
    811/1000 <= z <= 812/1000 ->
    2*z*(z^2-3)*(z^4+4*z^2-1)/((z-1)*(z+1)*(z^2+1)*(z^2-2*z-1)*(z^2+2*z-1)) < 0.
Proof.
  intros. interval with (i_bisect_diff z).
Qed.

(* Since fL is decreasing on [0.811, 0.812], fL - k has at most one root there
   for any real k. fL - fU(sqrt(1/3)) has such a root by the intermediate value theorem.
   Since fL is differentiable, one could prove this constructively without an appeal to IVT.
   We will not do so now. *)

Ltac unfold_defs := unfold fU; unfold PHU; unfold FU;
                    unfold fL; unfold PHL; unfold FL;
                    unfold UB; unfold UB_igd;
                    unfold LB; unfold LB_igd;
                    unfold K; unfold S; unfold asinh.

Lemma fU_xi_bounds:
  686533 / 1000000 < fU(sqrt(1/3)) < 686537 / 1000000.
Proof.
  split; unfold_defs; interval.
Qed.

Lemma fL_xi_bounds:
  fL(8112/10000) > 686537/1000000 /\ fL(8113/10000) < 686533/1000000.
Proof.
  split; unfold_defs; interval.
Qed.

(* Therefore, by the intermediate value theorem,
   there is a unique point xi between 0.8112 and
   0.8113 such that fL(xi) = fU(sqrt(1/3)). *)

(* Now we get bounds on DV. We want a lemma
   of the form DV < TH -> fL(BL(DV)) < fU(sqrt(1/3)).
   
   We begin by showing it makes sense to consider this,
   since fU(sqrt(1/3)) is in the domain of invertibility of fL
   near 1 (viz., [sqrt(sqrt(5)-2), infty]).
*)

Lemma fU_sqrt_DV_bounds:
  fU(sqrt(1/3)) > sqrt(sqrt(5)-2).
Proof.
  unfold_defs. interval.
Qed.

(* fL(BL(DV)) < fU(sqrt(1/3)) is implied by
   fL(BL(DV)) < 0.686533, since 0.686533 < fU(sqrt(1/3)).
   
   We show next that fL(x) < 0.686533 is implied by
   x > 0.81127. We can do this just by showing fL(0.81127) < 0.686533,
   since fL is decreasing on [sqrt(sqrt(5)-2), infty).
*)
Lemma fL_DV_bounds:
  fL(81127/100000) < 686533/1000000.
Proof.
  unfold_defs; interval.
Qed.

(* Finally we want some way to imply BL(DV) > 0.81127, which is
   to say (since LB is decreasing on (sqrt(sqrt(5)-2), 1))
   DV < LB(0.81127). If TH < LB(0.81127) we can imply this by
   DV < TH. It suffices to pick TH = 0.15326.
 *)

Lemma DV_bounds:
  15326/100000 < LB(81127/100000).
Proof.
  unfold_defs; interval.
Qed.

(* And finally, now for the bounds on alpha, beta, and gamma.
   
   For the bound on alpha, we rewrite PHU(xi) - PHL(xi) as
   a single integral, rewriting the integrand. By grinding from
   Maxima, we get that this integrand is as given below. After
   loading pams.mac, the command that gets us the definition below is

   grind(factor(expand(FU - FL)));

 *)

Definition alpha_igd z := 8*z*(z^4+4*z^2-1)/((z^2+1)^2*(z^2-2*z-1)*(z^2+2*z-1)).

(* We can't define alpha, since we haven't defined xi yet.
   So instead we will just derive an upper bound on alpha. *)

Lemma alpha_igd_ineq : forall z, 81127/100000 <= z <= 1 -> (alpha_igd z) < 0.
Proof.
  intros. unfold alpha_igd.
  interval with (i_bisect_diff z).
Qed.

(* Let A(z) be the integral of alpha_igd from 1 to z. Then
   A'(z) = alpha_igd(z). So A is decreasing (on [sqrt(1/3),1]).
   Hence A(xi-eps) is an upper bound on A(xi) for small eps > 0.
   Likewise 1-xi+eps is an upper bound on 1-xi for eps > 0.
   We pick eps = xi - 0.81127. Also, since TH < Theta, 1/TH > 1/Theta.
 *)

Check PI.

Lemma alpha_bound :
  (K * (1 - 81127/100000)/(2*PI*15326/100000))
  * exp (RInt alpha_igd 1 (81127/100000)) < 97/100.
Proof.
  unfold alpha_igd. unfold_defs.
  interval.
Qed.

(* In fact, beta is (2*pi)^2*Theta/fL(xi). So to get an
   upper bound on beta, we get an upper bound on Theta
   and on fL(xi). We begin with an upper bound on Theta.
   Theta is LB(xi). Since LB is decreasing, LB(xi-eps)
   is greater than LB(xi) for eps > 0 small enough.
   So an upper bound on LB(0.8112) is an upper bound 
   on Theta.
 *)

Lemma theta_upper_bound :
  LB(8112/10000) < 1562/10000.
Proof.
  unfold_defs. interval.
Qed.

(* Next an upper bound on 1/fL(xi). Since 
   fL is decreasing, 1/fL is increasing.
   So 1/fL(xi) < 1/fL(xi+eps).
 *)

Lemma fL_inv_upper_bound :
  1 / (fL (8113/10000)) < 1457/100.
Proof.
  unfold_defs. interval.
Qed.

Lemma beta_bound :
  (2*PI)^2 * (1562/10000) * (1457/1000) > 895/100.
Proof.
  interval.
Qed.

(* Now for gamma. gamma is pi^2*e^(PHU(xi)).
   PHU' is FU. Now, FU is negative on the 
   given interval.
 *)

Lemma FU_neg:
  forall z, 811/1000 <= z <= 1 ->
            FU z < 0.
Proof.
  intros. unfold_defs. interval with (i_bisect_diff z).
Qed.

(* Therefore, PHU is a decreasing function there.
   So exp o PHU is likewise a decreasing function.
   So exp(PHU(xi-eps)) > exp(PHU(xi)) for eps > 0.
 *)

Lemma gamma_bound :
  PI^2 * exp(PHU(8112/10000)) < 134/10.
Proof.
  unfold_defs. interval.
Qed.

(* Finally for the slope bound. fU is decreasing,
   so 1/sqrt(fU(x)) is an increasing function of
   x; so 1/sqrt(fU(BU(TH))) < 1/sqrt(fU(BU(TH)+eps))
   for eps > 0 small. Hence if BU(TH) < BB then
   an upper bound on 1/sqrt(fU(BB)) will suffice.

   Now BU(TH) < BB when TH > UB(BB). So now we need
   a lower bound on Theta.
 *)

Lemma theta_lower_bound :
  LB(8113/10000) > 153/1000.
Proof.
  unfold_defs. interval.
Qed.

Lemma BB_bound :
  153/1000 > UB(758/1000).
Proof.
  unfold_defs. interval.
Qed.

(* So BB = 0.758 suffices. Thus finally we arrive
   at the following bound.
 *)

Lemma slope_bound :
  85/10 > 2*PI/sqrt(fU(758/1000)).
Proof.
  unfold_defs. interval.
Qed.
