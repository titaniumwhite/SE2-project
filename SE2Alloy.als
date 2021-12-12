//////////////////////////ENTITIES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sig PersonalCode{}


abstract sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	send: set Ticket,
	work: one Land,
	refersA: one Agronomist
}

sig Agronomist extends User{
	manage: one Land,
	send: set Alert,
	plan: one Calendar
}

sig PolicyMaker extends User{
}

sig Land{
	works: set Farmer,
	monitored: one Agronomist,
	useT: one Tablet,
	haveC: one Calendar
}

abstract sig Ticket{
	state: one State
}

abstract sig State{}
one sig ACCEPTED extends State{}
one sig PENDING extends State{}
one sig REJECTED extends State{}

sig RequestVisit extends Ticket{}

sig RequestHelp extends Ticket{}

sig DailyPlan{
	visit: set Farmer
}

sig Calendar{
	contains: set DailyPlan
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
	//no Agronomist manage different Lands
	all a:Agronomist | (no disj l1,l2:Land | a in l1.monitored and a in l2.monitored)
and //no Land is managed by different Agronomist
	all l:Land | (no disj a1,a2:Agronomist | l in a1.manage and l in a2.manage)
and	 //no land without an Agronomist
	all l:Land | one a:Agronomist | a in l.monitored
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
	#Agronomist = 3
	#Land = 3
	#DailyPlan = 5
}

run show for 10
