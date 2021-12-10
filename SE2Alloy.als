open util/time

//////////////////////////ENTITIES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sig PersonalCode{}

sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	use: one Tablet,
	send: set Ticket,
	work: one Land,
	refersA: one Agronomist
}

sig Agronomist extends User{
	manage: one Land,
	send: set Alert,
	plan: some DailyPlan 
}

sig PolicyMaker extends User{
}

sig Land{
	works: set Farmer,
	monitors: one Agronomist,
	useT: one Tablet,
	haveC: one Calendar
}

abstract sig Ticket{}

abstract sig VisitState{
	vmState: State lone -> Time,
	haveVisit: lone Visit
}

abstract sig State{}
one sig ACCEPTED extends State{}
one sig PENDING extends State{}
one sig REJECTED extends State{}

sig RequestVisit extends Ticket{}

sig RequestHelp extends Ticket{}

sig Visit extends VisitState{
	request: lone RequestVisit,
	inside: one DailyPlan,
	visitTime: one Time,
	landVisit: one Land,
	meet: one Farmer
}

sig DailyPlan{
	contains: set Visit,
}

sig Calendar{
	contains: set DailyPlan,
	belongA: one Agronomist,
	belongL: one Land
}

sig Tablet{}

sig Alert{}

////////////////////////////////////////FACTS\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\


//every User's personal code is unique and belongs to only one user
fact noEqualPersonalCode{
	all disj u,u':User | u.userPersonalCode != u'.userPersonalCode
}

//every personal code must be related to an User
fact noPersonalCodeWOUser{
	all pc:PersonalCode | let u=User | (pc in u.userPersonalCode)
}


fact landAgronomist{
	// no Agronomist that works for different lands
	all a:Agronomist | (no disj l1,l2:Land | a in l1.monitors and a in l2.monitors)
and //no land without an Agronomist
	all l:Land | one a:Agronomist | a in l.monitors
and	// no Agronomist without a land
	all a:Agronomist | one l:Land | l in a.manage
}

fact landFarmer{
	//no Farmer that works in differents lands
	all f:Farmer | (no disj l1,l2:Land | f in l1.works and f in l2.works)
and //no land without Farmer
	all l:Land | one f:Farmer | f in l.works
and //no Farmer without a land
	all f:Farmer | one l:Land | l in f.work
}

pred show{}

run show for 2
