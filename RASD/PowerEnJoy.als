open util/boolean 


// SIGNATURES
sig Position{}

one sig SafeArea{
	position: set Position	
}

// a vehicle can be parked in a PowerStation also if the vehicle is not inCharge
sig PowerStation{
	position : one Position,
	vehicles : set Vehicle,
	capacity : one Int
}{
	capacity >= #vehicles
	capacity < 5 // For istance
	vehicles.position = position
}

// We have ignored many useless information for the user like email, driving license
sig User{	
	position: one Position,
	reservation: lone Reservation,
	isInBlackList: one Bool
}{
	isInBlackList.isTrue implies #reservation=0
}

sig Technician {
	isTakingCareOf: lone Vehicle
}{
	isTakingCareOf.state in InProcessing
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
time<60
}

sig Ride{
	passengersNumber: one Int,
	vehicle: one Vehicle,
	user: one User
}
{
	passengersNumber>0 && passengersNumber<=5 
	vehicle.state in InUse
	#user.reservation=0
	user.isInBlackList.isFalse
}

abstract sig VehicleState{}
one sig Available extends VehicleState{}
one sig Reserved extends VehicleState{}
one sig InUse extends VehicleState{}
one sig NotAvailable extends VehicleState{}
one sig LowBattery extends VehicleState{}
one sig InProcessing extends VehicleState{}

//FACTS

fact reservationHasOneUser{
	all disj u1,u2: User | u1.reservation!=u2.reservation
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

fact aPowerStationIsAlwaysInASafeArea{
	all p:PowerStation | p.position in SafeArea.position
}

fact aVehicleInChargeIsInAPowerStation {
	all v:Vehicle | v.isInCharge.isTrue implies one p:PowerStation | v in p.vehicles
}

fact ifAUserIsInAVehicleHeHasTheSamePosition{
	all r:Ride | r.vehicle.position = r.user.position
}

fact thePositionOfAPowerStationIsUnique {
	all p1,p2 :PowerStation | p1!=p2 implies p1.position != p2.position
}

fact technicianWork{
	all v:Vehicle | v.state in InProcessing implies one t:Technician | v in t.isTakingCareOf 
}

// ASSERTIONS

assert allTheVehiclesNotIgnitedAreInASafeArea{
	all v:Vehicle | v.isIgnited.isFalse implies v.position in SafeArea.position
}


assert numberOfTheRidesAreCorrect{
	#Ride = #{v:Vehicle | v.state in InUse}
}


assert numberOfTheReservationsAreCorrect{
	#Reservation = #{v:Vehicle | v.state in Reserved}
}


assert blackListUser{
	all r:Ride | r.user.isInBlackList.isFalse
	all u:User | u.isInBlackList.isTrue implies u.reservation = none
}

assert numberOfTechniciansIsGreaterOrEqualThanInProcessingVehicles{
	#Technician >= #{v:Vehicle | v.state in InProcessing}
}


check allTheVehiclesNotIgnitedAreInASafeArea for 8 Int
check numberOfTheRidesAreCorrect for 8 Int
check numberOfTheReservationsAreCorrect for 8 Int
check blackListUser for 8 Int
check numberOfTechniciansIsGreaterOrEqualThanInProcessingVehicles for 8 Int

pred ShowVehiclesPossibleStates{
#Vehicle = 6
#User = 3
#Technician = 2
some v:Vehicle | v.state in Available
some v:Vehicle | v.state in Reserved
some v:Vehicle | v.state in NotAvailable
some v:Vehicle | v.state in InUse
some v:Vehicle | v.state in InProcessing
some v:Vehicle | v.state in LowBattery
}

// the 3 vehicles are all parked in the powerStation but can be not plugged in
pred ShowAFullPowerStation{
	#PowerStation=1
	#Vehicle = 3
	one p:PowerStation | p.capacity = #p.vehicles and p.capacity=3
}

pred Show{}


run ShowVehiclesPossibleStates for 6 but 8 Int
run ShowAFullPowerStation for 3 but 8 Int
run Show for 4 but 8 Int
