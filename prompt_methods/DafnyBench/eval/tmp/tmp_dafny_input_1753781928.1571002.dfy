
method DPGD_GradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
  requires iterations>=0
  requires size>=0
  requires noise_scale >= 1.0
  requires -1.0 <= gradient_norm_bound <= 1.0
{
  var thetha:array<real> := new real[iterations+1];
  thetha[0] := *;
  var alpha:real := 0.0;
  var tau:real := *;
  assume(tau>=0.0);
  var t :int := 0;
  var constant:real := (size as real) * tau;
  while (t < iterations)
    invariant 0 <= t <= iterations
    invariant thetha != null && thetha.Length == iterations+1
    invariant alpha >= 0.0
    invariant forall k :: 0 <= k <= t ==> thetha[k] == *
  {
    var i :int := 0;
    var beta:real := 0.0;
    var summation_gradient:real := 0.0;
    while (i< size)
      invariant 0 <= i <= size
      invariant beta == tau * i
      invariant summation_gradient == *
    {
      var gradient:real := *;
      // Note: We do not need to clip the value of the gradient.
      // Instead, we clip the sensitivity of the gradient by the gradient_norm_bound provided by the user
      var eta:real := *;
      beta := beta + tau;
      var eta_hat:real := - gradient_norm_bound;
      summation_gradient := summation_gradient + gradient + eta;
      i := i + 1;
    }
    alpha := alpha + beta;
    thetha[t+1] := thetha[t] - learning_rate*summation_gradient;
    t := t+1;
  }
  Para := thetha[iterations];
  PrivacyLost := alpha;
}

function abs(a: real) : real {if a>0.0 then a else -a}
