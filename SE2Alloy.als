//////////////////////////ENTITIES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sig PersonalCode{}


abstract sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	sendT: set Ticket,
	work: one Land
}

sig Agronomist extends User{
	monitors: one Land,
	sendA: set Alert,
	plan: one Calendar,
	receiveT: set Ticket
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

abstract sig Ticket{
//	state: one State
	ticketSentBy: one Farmer,
	ticketSentTo: one Agronomist
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

////////////////////////////////////WIP\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
//TODO: correggere noDailyPlanWOCalendar


fact visitFarmer {
	// The DailyPlan of an Agronomist have to visit only the Farmers monitored by the Agronomist [CORRETTO?]
	all d:DailyPlan | all a:Agronomist, f:Farmer | (d in a.plan.contains) implies (d in contains[plan[isMonitored[f.work]]])
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

fact reportToAgronomist{
	// A Report sent by a Policy Maker have to be sent to the Agronomist of the Farmer 
	all r:Report | all f:Farmer | (f in r.refersTo) implies (f.work.isMonitored in r.sentTo)
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

fact ticketToAgronomist{
	ticketSentBy = ~sendT and ticketSentTo = ~receiveT
and //A Ticket sent by a Farmer can only be sent to the Agronomist of the Farmer's Land
	all f:Farmer, t:Ticket | (t in f.sendT) implies (t in receiveT[isMonitored[f.work]])
}

//no Calendar WO Agronomist
fact calendarAgronomist{
	all c:Calendar | one a:Agronomist | c in a.plan
}

//no DailyPlan WO Calendar !!!!!!!!!!!!!!
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
	#DailyPlan = 7
	#Farmer = 5
	#Agronomist = 3
}

run show for 10 but 0 PolicyMaker 
