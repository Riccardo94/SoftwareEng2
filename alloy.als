open util/boolean 

sig Position{
	latitude: Int, //float
	longitude: Int //float
}

sig PaymentMethod{}

sig SafeArea{}

abstract sig Parking{}

/*sig PowerStation extends Parking{
	position = one Position
}*/

sig LegalParking extends Parking{}

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
	isIgnited = True <=> state in InUse
	isInCharge = True => state in VehicleState - InUse
}

fact stateWithLowBattery{
	all v:Vehicle | v.batteryLevel<20 => v.state in LowBattery
}

fact LowBatteryVehicleNotReserved{
	no r:Reservation | r.vehicle.batteryLevel<20 //non va e non so perchè
}

sig Reservation{
	time: one Int,
	vehicle: one Vehicle
}
{vehicle.state in Reserved}

sig Ride{
	passengersNumber: one Int,
	moneyToCharge: one Int,
	vehicle: one Vehicle,
	user: one User
}
{
	passengersNumber>0 && passengersNumber<5 && moneyToCharge>0
	vehicle.state in InUse
}

fact reservationHasOneUser{
	all r:Reservation, u,u1:User | (u.reservation=r && u!=u1) => u1.reservation!=r
	//all r:Reservation | one u:User | u.reservation=r
}

fact vehicleHasOneReservation{
	all v:Vehicle, r,r1:Reservation | (r.vehicle=v && r!=r1) => r1.vehicle!=v
	//all v:Vehicle | one r:Reservation | v.state in Reserved => r.vehicle=v
}

fact vehicleInUseHasNoReservation{
	all v:Vehicle, r:Reservation | v.state in InUse => r.vehicle!=v
} 

fact userWithRideHasNoReservation{
	all r:Ride,u:User | r.user=u => #u.reservation=0
	all r:Reservation,ri:Ride,u:User | u.reservation=r => #ri.user=0
}

fact userHaveOneRide{
	all u:User, r,r1:Ride | (r.user=u && r!=r1) => r1.user!=u
}

fact vehicleInUseHasOneRide{
//	all v:Vehicle | one r:Ride | v.state in InUse => r.vehicle=v
}

abstract sig VehicleState{}
one sig Available extends VehicleState{}
one sig Reserved extends VehicleState{}
one sig InUse extends VehicleState{}
one sig NotAvailable extends VehicleState{}
one sig LowBattery extends VehicleState{}
one sig InProcessing extends VehicleState{}

pred Show{}

run Show for 3


