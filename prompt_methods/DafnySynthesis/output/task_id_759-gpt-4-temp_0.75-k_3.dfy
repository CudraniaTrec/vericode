method IsDecimalWith2Precision(s: string) returns (isValid: bool)
{
  // A valid decimal with 2 precision is of the form: [digits]+ '.' [digits][digits]
  if |s| < 4 then
    return false;
  var dotIndex := s.IndexOf(".");
  if dotIndex == -1 then
    return false;
  // There must be at least one digit before the dot
  if dotIndex < 1 then
    return false;
  // There must be exactly 2 digits after the dot
  if dotIndex + 3 != |s| then
    return false;
  // Check all chars before the dot are digits
  var i := 0;
  while i < dotIndex
    invariant 0 <= i <= dotIndex
    invariant i <= |s|
    invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
  {
    if !( '0' <= s[i] <= '9' ) then
      return false;
    i := i + 1;
  }
  // Check both chars after the dot are digits
  if !( '0' <= s[dotIndex + 1] <= '9' && '0' <= s[dotIndex + 2] <= '9' ) then
    return false;
  return true;
}