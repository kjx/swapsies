

trait Sensor {
    opaque ghost predicate dodgy()
    ghost const underlyingTruth : nat := 0
    function value() : (r : nat)
     ensures not(dodgy()) ==> r == underlyingTruth
}

const MAX_SENSOR := 10

//this works but note the details
method getValue(sensor : Sensor) returns (r : set<nat>)
   ensures not(sensor.dodgy()) && (sensor.value() < MAX_SENSOR)  ==> (r == {sensor.underlyingTruth})
{
    if (sensor.value() >= MAX_SENSOR)
    {
        print "sensor out of range warning\n";
        return {};
    } else {
        return {sensor.value()};
    }
}



// //note this does NOT work (as it should not)
// method getValueX(sensor : Sensor) returns (v : set<nat>)
// {
//     if (sensor.dodgy())
//     {
//         print "dodgy sensor\n";
//         return {};
//     } else {
//         return {sensor.value()};
//     }
// }








predicate not(x : bool) { !x }