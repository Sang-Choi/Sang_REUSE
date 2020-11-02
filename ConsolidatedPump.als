open util/ordering[Pump]

abstract sig Rate{}
one sig NotSetR, LowR, MediumR, HighR extends Rate{}

abstract sig Capacity {}
one sig NotSetC, LowC, MediumC, HighC extends Capacity{}

abstract sig Power {}
one sig Plugged, Unplugged extends Power{}

abstract sig Locking {}
one sig Locked, Unlocked extends Locking{}

abstract sig Infuse {}
one sig InfusionComplete, Infusing, NotInfusing extends Infuse{}
 
sig Pump {
	rate: one Rate,
	cap: one Capacity,
	plug: one Power,
	lock: one Locking,
	infuseState: one Infuse
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
  p.rate = p'.rate
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

run {last.infuseState=InfusionComplete} for 15 Pump
