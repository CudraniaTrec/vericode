class {:autocontracts} CarPark {
    const totalSpaces: nat := 10;
    const normalSpaces: nat:= 7;
    const reservedSpaces: nat := 3;
    const badParkingBuffer: int := 5;

    var weekend: bool;
    var subscriptions: set<string>;
    var carPark: set<string>;
    var reservedCarPark: set<string>;

    constructor()
    requires true
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false;
    {
      this.subscriptions := {};
      this.carPark := {};
      this.reservedCarPark := {};
      this.weekend := false;
      // No assertions or reads of fields allowed here except assignments
    }

    ghost predicate Valid()
    reads this
    {
      carPark * reservedCarPark == {} &&
      |carPark| <= totalSpaces + badParkingBuffer &&
      (normalSpaces + reservedSpaces) == totalSpaces &&
      |reservedCarPark| <= reservedSpaces
    }

    method leaveCarPark(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> (((car in old(carPark)) && carPark == old(carPark) - {car} && reservedCarPark == old(reservedCarPark)) || ((car in old(reservedCarPark)) && reservedCarPark == old(reservedCarPark) - {car} && carPark == old(carPark)));
    ensures success ==> (car !in carPark) && (car !in reservedCarPark);
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && (car !in old(carPark)) && (car !in old(reservedCarPark));
    ensures subscriptions == old(subscriptions) && weekend == old(weekend);
    {
      success := false;

      // Invariant: carPark and reservedCarPark are always disjoint
      assert carPark * reservedCarPark == {};

      if car in carPark {
        // car is in carPark, not in reservedCarPark
        assert car !in reservedCarPark;
        carPark := carPark - {car};
        success := true;
        assert car !in carPark;
        assert reservedCarPark == old(reservedCarPark);
      } else if car in reservedCarPark {
        // car is in reservedCarPark, not in carPark
        assert car !in carPark;
        reservedCarPark := reservedCarPark - {car};
        success := true;
        assert car !in reservedCarPark;
        assert carPark == old(carPark);
      }
      // Postconditions
      if success {
        assert (car !in carPark) && (car !in reservedCarPark);
      } else {
        assert carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
        assert (car !in old(carPark)) && (car !in old(reservedCarPark));
      }
      assert subscriptions == old(subscriptions);
      assert weekend == old(weekend);
    }

    method checkAvailability() returns (availableSpaces: int)
    requires true
    modifies this
    ensures weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) + (reservedSpaces - old(|reservedCarPark|)) - badParkingBuffer;
    ensures !weekend ==> availableSpaces == (normalSpaces - old(|carPark|)) - badParkingBuffer;
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions);
    {
      if (weekend){
        availableSpaces := (normalSpaces - |carPark|) + (reservedSpaces - |reservedCarPark|) - badParkingBuffer;
        assert availableSpaces == (normalSpaces - old(|carPark|)) + (reservedSpaces - old(|reservedCarPark|)) - badParkingBuffer;
      } else{
        availableSpaces := (normalSpaces - |carPark|) - badParkingBuffer;
        assert availableSpaces == (normalSpaces - old(|carPark|)) - badParkingBuffer;
      }
      assert carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions);
    }

    method makeSubscription(car: string) returns (success: bool)
    requires true
    modifies this
    ensures success ==> old(|subscriptions|) < reservedSpaces && car !in old(subscriptions) && subscriptions == old(subscriptions) + {car};
    ensures !success ==> subscriptions == old(subscriptions) && (car in old(subscriptions) || old(|subscriptions|) >= reservedSpaces);
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);
    {
      if |subscriptions| >= reservedSpaces || car in subscriptions {
        success := false;
        assert subscriptions == old(subscriptions);
      } else {
        subscriptions := subscriptions + {car};
        success := true;
        assert subscriptions == old(subscriptions) + {car};
      }
      if success {
        assert old(|subscriptions|) < reservedSpaces;
        assert car !in old(subscriptions);
        assert subscriptions == old(subscriptions) + {car};
      } else {
        assert subscriptions == old(subscriptions);
        assert (car in old(subscriptions) || old(|subscriptions|) >= reservedSpaces);
      }
      assert carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);
    }

    method openReservedArea()
    requires true
    modifies this
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == true && subscriptions == old(subscriptions);
    {
      weekend := true;
      assert carPark == old(carPark);
      assert reservedCarPark == old(reservedCarPark);
      assert subscriptions == old(subscriptions);
      assert weekend == true;
    }

    method closeCarPark()
    requires true
    modifies this
    ensures carPark == {} && reservedCarPark == {} && subscriptions == {}
    ensures weekend == old(weekend);

    {
      var oldWeekend := weekend;
      carPark := {};
      reservedCarPark := {};
      subscriptions := {};
      assert carPark == {};
      assert reservedCarPark == {};
      assert subscriptions == {};
      assert weekend == oldWeekend;
    }

    method enterCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|carPark|) < normalSpaces - badParkingBuffer);
    ensures success ==> carPark == old(carPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|carPark|) >= normalSpaces - badParkingBuffer));
    ensures subscriptions == old(subscriptions) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend);

    {
      if (|carPark| >= normalSpaces - badParkingBuffer || car in carPark || car in reservedCarPark) {
        return false;
      }
      else
      {
        carPark := carPark + {car};
        return true;
      }
    }

    method enterReservedCarPark(car: string) returns (success: bool)
    requires true
    modifies this;

    ensures success ==> (car !in old(carPark)) && (car !in old(reservedCarPark)) && (old(|reservedCarPark|) < reservedSpaces) && (car in subscriptions || weekend == true);
    ensures success ==> reservedCarPark == old(reservedCarPark) + {car};
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark);
    ensures !success ==> (car in old(carPark)) || (car in old(reservedCarPark) || (old(|reservedCarPark|) >= reservedSpaces) || (car !in subscriptions && weekend == false));
    ensures subscriptions == old(subscriptions) && carPark == old(carPark) && weekend == old(weekend);
    ensures weekend == old(weekend) && subscriptions == old(subscriptions);

    {
      if (|reservedCarPark| >= reservedSpaces || car in carPark || car in reservedCarPark || (car !in subscriptions && weekend == false)) {
        return false;
      }
      else
      {
        reservedCarPark := reservedCarPark + {car};
        return true;
      }
    }
}

method Main() {
  var carPark := new CarPark();

  var availableSpaces := carPark.checkAvailability();

  var success := carPark.enterCarPark("car1");
  availableSpaces := carPark.checkAvailability();

  success := carPark.enterCarPark("car2");
  availableSpaces := carPark.checkAvailability();

  success := carPark.enterCarPark("car3");

  success := carPark.makeSubscription("car4");

  success := carPark.enterReservedCarPark("car4");
  success := carPark.enterReservedCarPark("car5");

  success := carPark.makeSubscription("car6");
  success := carPark.makeSubscription("car7");
  success := carPark.makeSubscription("car8");

  success := carPark.enterReservedCarPark("car6");
  success := carPark.enterReservedCarPark("car7");

  success := carPark.leaveCarPark("car1");

  success := carPark.leaveCarPark("car9");

  success := carPark.leaveCarPark("car6");

  carPark.closeCarPark();
}

method MainB () {
  var carPark := new CarPark();

  carPark.openReservedArea();

  var success := carPark.enterReservedCarPark("car3");

  carPark.closeCarPark();
}

function abs(a: real) : real {if a>0.0 then a else -a}
