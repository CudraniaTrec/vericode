method SplitAndRotate<T>(l: seq<T>, n: nat) returns (res: seq<T>)
    requires n <= |l|
    ensures res == l[n..] + l[..n]
{
    res := l[n..] + l[..n];
}