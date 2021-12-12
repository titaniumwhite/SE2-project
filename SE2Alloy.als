//////////////////////////ENTITIES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sig PersonalCode{}


abstract sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	send: set Ticket,
	work: one Land
}

sig Agronomist extends User{
	monitors: one Land,
	send: set Alert,
	plan: one Calendar,
	receive: set Ticket
}

sig PolicyMaker extends User{
	send: some Report
}

sig Report{
	refersTo: one Farmer,
	sentTo: one Agronomist
}

sig Land{
	isWorked: set Farmer,
	isMonitored: one Agronomist,
	useT: one Tablet
}

abstract sig Ticket{}

abstract sig State{}
one sig ACCEPTED extends State{}
one sig PENDING extends State{}
one sig REJECTED extends State{}

sig RequestVisit extends Ticket{}

sig RequestHelp extends Ticket{
	sentBy: one Farmer,
	sentTo: one Agronomist
}

sig DailyPlan{
	visit: set Farmer
}

sig Calendar{
	contains: set DailyPlan
}

sig Tablet{}

sig Alert{}

////////////////////////////////////////FACTS\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

////////////////////////////////////WIP\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

fact requestHelpToAgronomist{
	sentBy = ~send and sentTo = ~receive
and //A Ticket sent by a Farmer can only be sent to the Agronomist of the Farmer's Land
	all f:Farmer, t:Ticket | (t in f.send) implies (t in receive[isMonitored[f.work]])
}


/////////////////////////////////////Done\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
//every User's personal code is unique and belongs to only one user
fact noEqualPersonalCode{
	all disj u,u':User | u.userPersonalCode != u'.userPersonalCode
}

//every personal code must be related to an User
fact noPersonalCodeWOUser{
	all pc:PersonalCode | let u=User | (pc in u.userPersonalCode)
}

fact policyMakerReport{
	//no Report WO PolicyMaker
	all r:Report | one p:PolicyMaker | r in p.send
}

fact landAgronomist{
	//no Agronomist monitors different Lands
	isMonitored = ~monitors
}

fact landFarmer{
	//no Farmer that works in differents lands
	isWorked =  ~work
}

//no Calendar WO Agronomist
fact calendarAgronomist{
	all c:Calendar | one a:Agronomist | c in a.plan
}

//no DailyPlan WO Calendar
fact calendarDailyPlan{
	all dp:DailyPlan | one c:Calendar | dp in c.contains 
}

//every tablet is unique and belongs to one Land
fact noTabletWOLand{
	all disj l1,l2:Land | l1.useT != l2.useT
and
	all t:Tablet | one l:Land | t in l.useT
}

pred show{
	#RequestHelp = 3
	#Agronomist = 2
	#Farmer = 3
}

run show for 10
