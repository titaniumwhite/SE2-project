sig PersonalCode{}

abstract sig User{
	userPersonalCode: one PersonalCode
}

sig Farmer extends User{
	sendT: set Ticket,
	work: one Land,
	isVisited: set Visit
} {#isVisited > 1}

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

abstract sig State{}
sig ACCEPTED extends State{}
sig PENDING extends State{}
sig REJECTED extends State{}


abstract sig Ticket{
	ticketSentBy: one Farmer,
	ticketSentTo: one Agronomist
}

sig RequestVisit extends Ticket{
	state: one State,
	visit: lone Visit
}

sig RequestHelp extends Ticket{}

sig Visit{
	visit: one Farmer
}

sig DailyPlan{
	containsVisit: set Visit,
} {#containsVisit <= 5}

sig Calendar{
	containsDP: set DailyPlan,
	isPlanned: one Agronomist
}

sig Tablet{}

sig Alert{
	alertSentTo: one Land
}

//////////////////////////////////////// FACTS \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

fact {
	plan= ~isPlanned		//no Agronomist plan different Calendars
	isVisited = ~visit			//no Farmer visited by different Visit
	isWorked =  ~work		//no Farmer that works in differents lands
	isMonitored = ~monitors 	//no Agronomist monitors different Lands
	ticketSentBy = ~sendT		//no Ticket sent from different Farmers
	ticketSentTo = ~receiveT	//no Ticket sent to different Agronomist
}

//every User's personal code is unique and belongs to only one user
fact noEqualPersonalCode{
	all disj u,u':User | u.userPersonalCode != u'.userPersonalCode
}

//every personal code must be related to an User
fact noPersonalCodeWOUser{
	all pc:PersonalCode | let u=User | (pc in u.userPersonalCode)
}

// A Report sent by a Policy Maker have to be sent to the Agronomist of the Farmer 
fact reportToCorrectAgronomist{
	all r:Report | all f:Farmer | (f in r.refersTo) implies (f.work.isMonitored in r.sentTo)
}

 //A Ticket sent by a Farmer can only be sent to the Agronomist of the Farmer's Land
fact ticketToCorrectAgronomist{
	all f:Farmer, t:Ticket | (t in f.sendT) implies (t in receiveT[isMonitored[f.work]])
}

//There is no Report without a PolicyMaker
fact noReportWOPolicyMaker{
	all r:Report | one p:PolicyMaker | r in p.send
}

//There is no Calendar without an Agronomist
fact noCalendarWOAgronomist{
	all c:Calendar | one a:Agronomist | c in a.plan
}

//There is no Dailyplan withouth a Calendar
fact noDailyPlanWOCalendar{
	all dp:DailyPlan | one c:Calendar | dp in c.containsDP 
}

//There is no Visit without a DailyPlan
fact noVisitWODailyPlan{
	all v:Visit | one d:DailyPlan | v in d.containsVisit
}

//There is no Alert without an Agronomist
fact noAlertWOAgronomist{
	all al:Alert | one ag:Agronomist | al in ag.sendA
}

//There is no Tablet without a Land and the Tablet is unique
fact noTabletWOLand{
	all disj l1,l2:Land | l1.useT != l2.useT
	all t:Tablet | one l:Land | t in l.useT
}

fact alertAgronomist{
	//An Alert can't be sent by two different Agronomist
	all al:Alert | (no disj a1,a2:Agronomist | al in a1.sendA and al in a2.sendA)
	 //The Alert has to be sent to the Land monitored by the Agronomist who sent the Alert
	all al:Alert | all l:Land | (al in l.isMonitored.sendA) implies (al.alertSentTo in l)
}

//Create a Visit  to visit the Farmer if the VisitRequest has been ACCEPTED
fact createVisitIfRequestAccepted{
	all r:RequestVisit |  r.state = ACCEPTED implies (one v:Visit, f:Farmer | v in r.visit and v in f.isVisited)
}

fact noStateWTwoRequest{
	//A State can't be of two different VisitRequest
	all s:State | (no disj r1,r2:RequestVisit | s in r1.state and s in r2.state)
	 //Each State has to belong to a unique VisitRequest
	all s:State | one r:RequestVisit | s in r.state
}

fact visitFarmer {
	//A Visit can't be contained in two different DailyPlans
	all v:Visit | (no disj d1,d2:DailyPlan | v in d1.containsVisit and v in d2.containsVisit)
and	// In a DailyPlan, there can be only one Visit per Farmer 
	all f:Farmer | all dp:DailyPlan | (f in dp.containsVisit.visit) implies (no disj v1,v2:Visit | v1 in dp.containsVisit and v2 in dp.containsVisit and f in v1.visit and f in v2.visit)
and	// The Visit to a Farmer has to be done only from the Agronomist of the Farmer
	all v:Visit | all f:Farmer | (f in v.visit) implies (v in f.work.isMonitored.plan.containsDP.containsVisit )
}

pred show{
	
}

run show for 10



//////////////////////////////////////// ASSERTIONS \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

// Visiting the same Farmer more than once in the same DailyPlan is not allowed
assert noVisitSameFarmerSameDailyPlan{
	no f:Farmer | all d:DailyPlan |(all disj v1,v2:Visit | v1 in f.isVisited and v2 in f.isVisited  and v1 in d.containsVisit and v2 in d.containsVisit)
}

// An Agronomist can't visit a Farmer which does not work in the Land he monitors
assert noVisitFromAgronomistOfOtherLand{
	no f:Farmer | all a:Agronomist | f.work not in a.monitors and a.plan.containsDP.containsVisit in f.isVisited
}

// A Visit can't be contained in two different DailyPlan simultaneously
assert noVisitInTwoDailyPlan{
	no v:Visit | (all disj d1,d2:DailyPlan | v in d1.containsVisit and v in d2.containsVisit)
}

// A Ticket of a Farmer can't be sent to an Agronomist which monitors a Land in which the Farmer does not work
assert noTicketSentToAgronomistOfOtherLand{
	no t:Ticket | all f:Farmer | t in f.sendT and f.work not in t.ticketSentTo.monitors
}

// A Report of a PolicyMaker can't be send to an Agronomist which monitors a Land in which the Farmer (subject of the report) does not work
assert noReportSentToAgronomistOfOtherLand{
	no r:Report | r.sentTo.monitors not in r.refersTo.work
}

// A Visit generated by an ACCEPTED RequestVisit can't be done to a Land in which the Farmer (who sent the RequestVisit) does not work
assert noVisitDueToRequestVisitToFarmerOfOtherLand{
	no v:Visit | one r:RequestVisit | one a:Agronomist | one f:Farmer | a not in f.work.isMonitored and a in r.ticketSentTo and f in r.ticketSentBy and v in r.visit and f in v.visit
}

check noVisitDueToRequestVisitToFarmerOfOtherLand



//////////////////////////////////////// PREDICATES \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

pred policyMakerCreateReport[p:PolicyMaker, r:Report, a:Agronomist]{
	p.send = r
	r.sentTo = a
	one f:Farmer | (f in a.monitors.isWorked) implies r.refersTo = f 
}

pred isDailyPlanNotFull[d:DailyPlan]{
	#(d.containsVisit) < 5
}

pred agronomistCreateAVisit[a:Agronomist, d:DailyPlan, v:Visit, f:Farmer]{
	isDailyPlanNotFull[d] 
	v in d.containsVisit
	f.work.isMonitored = a
	a.plan.containsDP = d
	implies
	f.isVisited = v
}

pred agronomistCreateAlert[ag:Agronomist, al:Alert, f:Farmer, l:Land]{
	ag in l.isMonitored
	f in l.isWorked
	ag.sendA = al
	al.alertSentTo = l
}

pred farmerMakeARequestHelp[f:Farmer, r:RequestHelp, a:Agronomist]{
	a in f.work.isMonitored
	r.ticketSentTo = a
	f.sendT = r
}

pred farmerMakeARequestVisitWhichIsAccepted[f:Farmer, r:RequestVisit, a:Agronomist, v:Visit]{
	a in f.work.isMonitored
	r.ticketSentTo = a
	f.sendT = r
	r.state = ACCEPTED
	r.visit = v
	v.visit = f
}

run policyMakerCreateReport
