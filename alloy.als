open util/boolean 

sig Position{}

sig PaymentMethod{}

one sig SafeArea{
	position: set Position	
}

/*sig PowerStation extends Parking{
	position = one Position
}*/


sig User{	
	position: one Position,
	reservation: lone Reservation
}

sig Vehicle{
	position: one Position,
	state: one VehicleState,
	batteryLevel: one Int,
	isIgnited: one Bool,
	isInCharge: one Bool,
	isLocked: one Bool
}
{
	batteryLevel>=0 && batteryLevel<=100
}


sig Reservation{
	time: one Int,
	vehicle: one Vehicle
}{
vehicle.state in Reserved
time>0
}

sig Ride{
	passengersNumber: one Int,
	moneyToCharge: one Int,
	vehicle: one Vehicle,
	user: one User
}
{
	passengersNumber>0 && passengersNumber<=5 && moneyToCharge>0
	vehicle.state in InUse
	#user.reservation=0
}

fact reservationHasOneUser{
<<<<<<< HEAD
	all r:Reservation, u,u1:User | (u.reservation=r && u!=u1) => u1.reservation!=r
=======
	all disj u1,u2: User | u1.reservation!=u2.reservation
>>>>>>> eefab7d07533d073efb2df811b562284d0ab58ef
	all r:Reservation | one u:User | u.reservation=r
}

fact vehicleReservedHasOneReservation{
	all disj r1,r2: Reservation | r1.vehicle!=r2.vehicle
	all v:Vehicle | v.state in Reserved => one r:Reservation | r.vehicle=v
}


fact userHaveOneRide{
	all disj r1,r2: Ride | r1.user != r2.user
}

fact vehicleInUseHasOneRide{
	all v:Vehicle | v.state in InUse => one r:Ride | r.vehicle=v
}

abstract sig VehicleState{}
one sig Available extends VehicleState{}
one sig Reserved extends VehicleState{}
one sig InUse extends VehicleState{}
one sig NotAvailable extends VehicleState{}
one sig LowBattery extends VehicleState{}
one sig InProcessing extends VehicleState{}

fact availableVehicle {
	all v1: Vehicle | v1.state in Available implies (v1.batteryLevel>20 and v1.isIgnited.isFalse and
	v1.isLocked.isTrue)
}

fact reservedVehicle {
	all v1: Vehicle | v1.state in Reserved implies ( v1.batteryLevel>20 and v1.isIgnited.isFalse)
}

fact inUseVehicle {
	all v1: Vehicle | v1.state in InUse implies (v1.isIgnited.isTrue and v1.isInCharge.isFalse)
}

fact lowBatteryVehicle {
	all v1: Vehicle | v1.state in LowBattery implies (v1.batteryLevel<20 and
	v1.isIgnited.isFalse and v1.isLocked.isTrue)
}

fact inProcessingVehicle {
	all v1: Vehicle | v1.state in InProcessing implies (v1.batteryLevel<20 and
	v1.isInCharge.isFalse)
}

fact aCarIsAlwaysParkedInASafeArea{
	all v1:Vehicle | v1.isIgnited.isFalse implies v1.position in SafeArea.position
}



pred Show{
#Vehicle=6
some v:Vehicle | v.state in InUse and v.position & SafeArea.position = none

}

run Show for 6 but 8 Int


