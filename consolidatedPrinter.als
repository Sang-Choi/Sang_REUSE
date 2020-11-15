open util/ordering[State]

sig State {
    orientation: one Orientation,
    color: one Color,
    printCount: one PrintCount,
    printSide: one PrintSide,
    connected: one Connected,
    printerOn: one PrinterOn,
    documentOpen: one DocumentOpen,
    printState: one PrintState
}

abstract sig PrintState{}
one sig NotPrinting, Printing, PrintingComplete extends PrintState{}

abstract sig Orientation{}
one sig NotSetO, Portrait, Landscape extends Orientation{}

abstract sig Color{}
one sig NotSetCol, BAndW, Colored extends Color{}

abstract sig PrintCount{}
one sig NotSetP, One, Multi extends PrintCount{}

abstract sig PrintSide{}
one sig NotSetS, Single, Double extends PrintSide{}

abstract sig Connected{}
one sig isConnected, NotConnected extends Connected{}

abstract sig PrinterOn{}
one sig On, Off extends PrinterOn{}

abstract sig DocumentOpen{}
one sig Open, NotOpen extends DocumentOpen{}

pred connection(s,s': State){
     s.printState = s'.printState
     s.printState = NotPrinting
     s.printerOn = s'.printerOn
     s.connected != s'.connected
     s.documentOpen = s'.documentOpen
     s.printCount = NotSetP
     s.printCount = s'.printCount
     s.color = NotSetCol
     s.color = s'.color
     s.printSide = NotSetS
     s.printSide = s'.printSide
     s.orientation = NotSetO
     s.orientation = s'.orientation
}

pred power(s, s': State){
     s.printState = s'.printState
     s.printState = NotPrinting
     s.documentOpen = s'.documentOpen
     s.connected = s'.connected
     s.printerOn != s'.printerOn
     s.color = s'.color
     s.color = NotSetCol
     s.printCount = s'.printCount
     s.printCount = NotSetP
     s.printSide = s'.printSide
     s.printSide = NotSetS
     s.orientation = s'.orientation
     s.orientation = NotSetO
}

pred openDoc(s, s': State){
     s.printState = s'.printState
     s.printState = NotPrinting
     s.connected = s'.connected
     s.documentOpen != s'.documentOpen
     s.printerOn = s'.printerOn
     s.color = NotSetCol
     s.printCount = NotSetP
     s.printSide = NotSetS
     s.orientation = NotSetO
     s.color = s'.color
     s.printCount = s'.printCount
     s.printSide = s'.printSide
     s.orientation = s'.orientation
}

pred setPrintSide(s, s': State){
    s.printState = s'.printState
    s.printState = NotPrinting
    s.connected = isConnected
    s.connected = s'.connected
    s.printerOn = On
    s.documentOpen = s'.documentOpen
    s.documentOpen = Open
    s.connected = s'.connected
     s.printerOn = s'.printerOn
     s.printSide != s'.printSide
     s.color = s'.color
     s.orientation = s'.orientation
     s.printCount = s'.printCount
}

pred setOrientation(s, s': State){
     s.printState = s'.printState
     s.printState = NotPrinting
     s.connected = isConnected
     s.printerOn = On
     s.documentOpen = Open
     s.connected = s'.connected
     s.printerOn = s'.printerOn
     s.documentOpen = s'.documentOpen
     s.color = s'.color
     s.orientation != s'.orientation
     s.printCount = s'.printCount
     s.printSide = s'.printSide
}

pred setColor(s, s': State){
     s.printState = s'.printState
     s.printState = NotPrinting
     s.connected = isConnected
     s.printerOn = On
     s.documentOpen = Open
     s.connected = s'.connected
     s.printerOn = s'.printerOn
     s.documentOpen = s'.documentOpen
     s.color != s'.color
     s.orientation = s'.orientation
     s.printCount = s'.printCount
     s.printSide = s'.printSide
}

pred setPrintCount(s, s': State){
     s.printState = NotPrinting
     s.printState = s'.printState
     s.connected = isConnected
     s.connected = s'.connected
     s.printerOn = On
     s.printerOn = s'.printerOn
     s.documentOpen = Open
     s.documentOpen = s'.documentOpen
     s.color = s'.color
     s.orientation = s'.orientation
     s.printCount != s'.printCount
     s.printSide = s'.printSide
}

pred startPrinting(s, s': State){
     s.connected = isConnected
     s.printerOn = On
     s.printState = NotPrinting
     s'.printState = Printing
     s.documentOpen = Open
     s.connected = s'.connected
     s.printerOn = s'.printerOn
     s.documentOpen = s'.documentOpen
     s.color != NotSetCol
     s.printSide != NotSetS
     s.printCount != NotSetP
     s.orientation != NotSetO
     s.color = s'.color
     s.orientation = s'.orientation
     s.printCount = s'.printCount
     s.printSide = s'.printSide
}

pred printComplete(s, s': State){
     s.connected = isConnected
     s.printerOn = On
     s.printState = Printing
     s'.printState = PrintingComplete
     s.documentOpen = Open
     s.color != NotSetCol
     s.printSide != NotSetS
     s.printCount != NotSetP
     s.orientation != NotSetO
     s.color = s'.color
     s.connected = s'.connected
     s.orientation = s'.orientation
     s.printerOn = s'.printerOn
     s.documentOpen = s'.documentOpen
     s.printCount = s'.printCount
     s.printSide = s'.printSide
}

fact {
     all s: State, s': s.next {
     	 setOrientation[s, s'] ||
	 setPrintCount[s, s'] ||
	 setPrintSide[s, s'] ||
	 setColor[s, s'] ||
	 power[s, s'] ||
	 connection[s, s'] ||
	 openDoc[s, s'] ||
	 printComplete[s, s'] ||
	 startPrinting[s, s']
      }
}
	 
pred initialState(s: State){
     s.connected = NotConnected
     s.printState = NotPrinting
     s.printerOn = Off
     s.documentOpen = NotOpen
     s.color = NotSetCol
     s.orientation = NotSetO
     s.printCount = NotSetP
     s.printSide = NotSetS
}

fact {
     first.initialState
}

run {last.printState = PrintingComplete} for 30 State

