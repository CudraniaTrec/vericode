//Dafny Code

method DeepCopySeq<T>(s: seq<T>) returns (copy: seq<T>)
  ensures copy == s
{
  // For value types (int, bool, etc.), seqs are immutable and copying is trivial
  // For reference types, this method will copy the references, not the objects themselves.
  // For a true "deep copy" of contained reference types, 
  // a user must provide a cloning function for T.
  copy := s[..];
}