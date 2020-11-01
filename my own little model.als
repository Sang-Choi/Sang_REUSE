open util/ordering[Pump]

one abstract sig Rate{}
sig NotSetR, LowR, MediumR, HighR extends Rate{}

one abstract sig Capacity {}
sig NotSetC, LowC, MediumC, HighC extends Capacity{}

one abstract sig Power {}
sig Plugged, Unplugged extends Power{}

one abstract sig Locking {}
sig Locked, Unlocked extends Locking{}

one abstract sig Infuse {}
sig InfusionComplete, Infusing, NotInfusing extends Infuse{}
 
one sig Pump {
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
	preSetup[p]
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
	p'.lock != p.lock
}


//Infusion happnes
pred preInfusionBegin(p: Pump){
	NotInfusing = p.infuseState
	Capacity = p.cap
	Rate = p.rate
}

pred InfusionBegin(p, p': Pump){
	preInfusionBegin[p]
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
	p1.infuseState = p2.infuseState
}

pred changeRate(p, p': Pump){
  p.rate = NotSetR 
  p'.rate != p.rate 
  p.cap = p'.cap 
  p.plug = p'.plug
  p.lock = p'.lock
  p.lock = Unlocked
  p.infuseState = p'.infuseState
  p.infuseState = NotInfusing
}

pred changeCap(p, p': Pump){
  p.rate = p'.rate
  p.cap = NotSetC
  p'.cap != p.cap
  p.plug = p'.plug
  p.lock = p'.lock
  p.lock = Unlocked
  p.infuseState = p'.infuseState
  p.infuseState = NotInfusing
}

pred changeLock(p, p': Pump){
  p.rate != NotSetR
  p.rate = p'.rate
  p.cap != NotSetC
  p.cap = p'.cap
  p.lock != p'.lock
  p.infuseState = NotInfusing
  p.infuseState = p'.infuseState
}

pred changePlug(p, p': Pump){
  p.plug != p'.plug
  p.rate = p'.rate
  p.cap = p'.cap
  p.lock = p'.lock
  p.infuseState = p'.infuseState
}

pred startInfusing(p, p': Pump){
  p.cap != NotSetC
  p.rate != NotSetR
  p.lock = Locked
  p.cap = p'.cap
  p.rate = p'.rate
  p.plug = p'.plug
  p.infuseState = NotInfusing
  p'.infuseState = Infusing
}

pred stopInfusing(p, p': Pump){
  p.cap != NotSetC
  p.rate != NotSetR
  p.lock = Locked
  p.cap = p'.cap
  p.rate = p'.rate
  p.plug = p'.plug
  p'.infuseState = NotInfusing
  p.infuseState = Infusing
}

pred infusionComplete(p, p': Pump){
  p.infuseState = Infusing
  p'.infuseState = InfusionComplete
}

pred reset(p, p': Pump){
  p.infuseState = InfusionComplete
  initialState[p']
  p.lock = p'.lock
}

pred initialState(p: Pump){
  p.rate = NotSetR
  p.cap = NotSetC
  p.infuseState = NotInfusing
  p.lock = Unlocked
}

fact {
  initialState[first]
  first.lock = Unlocked
}

fact {
  all p: Pump, p': p.next {
     changeRate[p, p'] ||
     changeCap[p, p'] ||
     changeLock[p, p'] ||
     changePlug[p, p'] ||
     startInfusing[p, p'] ||
     stopInfusing[p, p'] ||
     infusionComplete[p, p'] ||
     reset[p, p']
  }
}

