//Dafny Code

method Has30Days(month: int) returns (res: bool)
    requires 1 <= month <= 12
{
    // April (4), June (6), September (9), November (11) have 30 days
    if month == 4 || month == 6 || month == 9 || month == 11 {
        res := true;
    } else {
        res := false;
    }
}