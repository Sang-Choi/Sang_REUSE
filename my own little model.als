abstract sig Rate{}
one sig LowR, MediumR, HighR extends Rate{}

abstract sig Capacity {}
one sig LowC, MediumC, HighC extends Capacity{}

abstract sig Power {}
one sig Plugged, Unplugged extends Power{}

sig Locking {}
one sig Locked, Unlocked extends Locking{}

sig Infuse {}
one sig Infusing, NotInfusing extends Infuse{}
 
sig Pump {
	rate: one Rate,
	cap: one Capacity,
	plug: one Power,
	lock: one Locking,
	infuseState: one Infuse
}

pred preSetup(p:Pump){
	NotInfusing = p.infuseState
	Unlocked = p.lock
}
pred Setup(p, p':Pump, r: Rate, c: Capacity){
	preSetup(p)
	p'.rate = r
	p'.cap = c
	p'.rate != p.rate
	p'.cap != p.cap
	NotInfusing = p'.infuseState
	Unlocked = p'.lock
}

pred PowerSource(p, p':Pump) {
	p'.plug != p.plug
}

pred LineLock(p, p':Pump){
	p'lock != p.lock
}


//Infusion happnes
pred preInfusionBegin(p: Pump){
	NotInfusing = p.infuseState
	Capacity = p.cap
	Rate = p.rate
}

pred InfusionBegin(p, p': Pump){
	preInfusionBegin(p)
	p'.infuseState = Infusing
	p'.infuseState != p.infuseState
}

//Infusing completes
pred preInfusionComplete(p: Pump){
	Infusing = p.infuseState
}

pred InfusionComplete(p, p': Pump){
	p'.infuseState = NotInfusing
}
pred equivPump(p1,p2: Pump){
	p1.infuse = p2.infuse
}



