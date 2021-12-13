//////////////////////////ENTITIES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sig PersonalCode{}


abstract sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	sendT: set Ticket,
	work: one Land,
	isVisited: set Visit
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
// If RequestVisit == ACCEPTED, insert Visit in DailyPlan
one sig ACCEPTED extends State{}
one sig PENDING extends State{}
one sig REJECTED extends State{}

sig RequestVisit extends Ticket{}

sig RequestHelp extends Ticket{}

sig Visit{
	visit: one Farmer
}

sig DailyPlan{
	containsVisit: set Visit,
//	belongsTo: one Calendar
}

sig Calendar{
	containsDP: set DailyPlan,
	isPlanned: one Agronomist
}

sig Tablet{}

sig Alert{
	alertSentTo: one Land
}

////////////////////////////////////////FACTS\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

////////////////////////////////////////WIP\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\



/////////////////////////////////TO KEEP AN EYE ON\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

fact {
	plan= ~isPlanned and/* belongsTo = ~containsDP and*/ isVisited = ~visit
}

fact visitFarmer {
	//No Visit WO DailyPlan
	all v:Visit | one d:DailyPlan | v in d.containsVisit
and	// A Visit can be contained only in one DailyPlan
	all v:Visit | (no disj d1,d2:DailyPlan | v in d1.containsVisit and v in d2.containsVisit)
	//BUG: All the Visit refers to only one Calendar
and	// In a DailyPlan, there can be only one Visit per Farmer [IS BUG SOLVED????]
	all f:Farmer | all dp:DailyPlan | (f in dp.containsVisit.visit) implies (no disj v1,v2:Visit | v1 in dp.containsVisit and v2 in dp.containsVisit and f in v1.visit and f in v2.visit)
and	// The Visit to a Farmer has to be done only to the Agronomist's Farmers 
	all v:Visit | all f:Farmer | (f in v.visit) implies (v in f.work.isMonitored.plan.containsDP.containsVisit )
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

fact ticketToAgronomist{
	ticketSentBy = ~sendT and ticketSentTo = ~receiveT
and //A Ticket sent by a Farmer can only be sent to the Agronomist of the Farmer's Land
	all f:Farmer, t:Ticket | (t in f.sendT) implies (t in receiveT[isMonitored[f.work]])
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
	all dp:DailyPlan | one c:Calendar | dp in c.containsDP 
}

fact alertAgronomist{
	//An Alert can be sent only from a single Agronomist
	all al:Alert | (no disj a1,a2:Agronomist | al in a1.sendA and al in a2.sendA)
and //No Alert WO Agronomist
	all al:Alert | one ag:Agronomist | al in ag.sendA
and //The Alert has to be sent to the Agronomist's Land
	all al:Alert | all l:Land | (al in l.isMonitored.sendA) implies (al.alertSentTo in l)
}

//every tablet is unique and belongs to one Land
fact noTabletWOLand{
	all disj l1,l2:Land | l1.useT != l2.useT
and
	all t:Tablet | one l:Land | t in l.useT
}

pred show{
	#DailyPlan = 4
	#Visit = 7
	#Farmer = 5
	#Agronomist = 2
}

run show for 10 but 0 PolicyMaker 
