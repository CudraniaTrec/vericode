module U128 {
    import U64
    import opened Int

    // Read nth 64bit word out of this u128, where 0 identifies the most
    // significant word.
    function NthUint64(v:u128, k: nat) : u64
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (Int.TWO_64 as u128)) as u64
        else
            (v % (Int.TWO_64 as u128)) as u64
    }

    /**
     * Compute the log of a value at base 2 where the result is rounded down.
     */
    function Log2(v:u128) : (r:nat)
    ensures r < 128 {
        var low := (v % (Int.TWO_64 as u128)) as u64;
        var high := (v / (Int.TWO_64 as u128)) as u64;
        if high != 0 then U64.Log2(high)+64 else U64.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u128) : (r:nat)
    ensures r <= 15 {
        var low := (v % (Int.TWO_64 as u128)) as u64;
        var high := (v / (Int.TWO_64 as u128)) as u64;
        if high != 0 then U64.Log256(high)+8 else U64.Log256(low)
    }

    /**
     * Convert a u128 into a sequence of 16bytes (in big endian representation).
     */
    function ToBytes(v:u128) : (r:seq<u8>)
    ensures |r| == 16 {
        var low := (v % (Int.TWO_64 as u128)) as u64;
        var high := (v / (Int.TWO_64 as u128)) as u64;
        U64.ToBytes(high) + U64.ToBytes(low)
    }

    function Read(bytes: seq<u8>, address:nat) : u128
    requires (address+15) < |bytes| {
        var b1 := U64.Read(bytes, address) as u128;
        var b2 := U64.Read(bytes, address+8) as u128;
        (b1 * (Int.TWO_64 as u128)) + b2
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
