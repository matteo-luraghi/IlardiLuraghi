////////////////////// SIGNATURES

sig Student {
  	var applies: set Application,
	var participates: set Internship,
	var submits: set StudentFeedback,
	var writes: set StudentComment
}

sig Company {
  	var offers: set Internship,
  	var submits: set CompanyFeedback,
	var writes: set CompanyComment
}

var sig Internship {
  	var participants: set Student
} {
	one c: Company | this in c.offers
}

enum Status { APPROVED, REJECTED, PENDING }

var sig Application {
  	var status: one Status,
  	var refers: one Internship
} {
  one s: Student | this in s.applies
}

var sig StudentFeedback {
  	var about: one Internship
} {
  	one s: Student | this in s.submits
}

var sig CompanyFeedback {
  	var about: one Student
} {
  	one c: Company | this in c.submits
}

var sig StudentComment {
	var about: one CompanyFeedback
} {
	one s: Student | this in s.writes
}

var sig CompanyComment {
	var about: one StudentFeedback
} {
	one c: Company | this in c.writes
}

////////////////////// RELATIONSHIPS FACTS

fact ApplicationsDontChangeReference { 
	always ( all a: Application |
			always (a.refers = a.refers'))
}

fact StudentFeedbacksDontChangeSubject {
	always ( all sf: StudentFeedback |
			always (sf.about = sf.about'))
}

fact CompanyFeedbacksDontChangeSubject {
	always ( all cf: CompanyFeedback |
			always (cf.about = cf.about'))
}

fact StudentCommentDontChangeSubject {
	always ( all sc: StudentComment |
			always (sc.about = sc.about'))
}

fact CompanyCommentDontChangeSubject {
	always ( all cc: CompanyComment |
			always (cc.about = cc.about'))
}

// student participates is the opposite of 
//internship participants
fact InternshipParticipants {
  	always ( all s: Student, i: Internship |
    		s in i.participants iff
	    	i in s.participates)
}

// applications can't be deleted
fact NoApplicationDeletion {
	always ( all a: Application, s: Student |
			a in s.applies implies
			always a in s.applies)
}

// students remain participants of an internship once approved
fact StudentStayInInternships {
	always ( all s: Student, i: Internship |
			(i in s.participates implies
			always i in s.participates) and
			(s in i.participants implies
			always s in i.participants))
}

// student feedbacks can't change writer or be deleted
fact NoStudentFeedbackDeletion {
	always ( all sf: StudentFeedback, s: Student |
			sf in s.submits implies
			always sf in s.submits)
}

// company feedbacks can't change writer or be deleted
fact NoCompanyFeedbackDeletion {
	always ( all cf: CompanyFeedback, c: Company |
			cf in c.submits implies
			always cf in c.submits)
}

// student comments can't change writer or be deleted
fact NoStudentCommentDeletion {
	always ( all sc: StudentComment, s: Student |
			sc in s.writes implies
			always sc in s.writes)
}

// company comments can't change writer or be deleted
fact NoCompanyCommentDeletion {
	always ( all cc: CompanyComment, c: Company |
			cc in c.writes implies
			always cc in c.writes)
}

// internships can't change owner or be deleted
fact NoInternshipDeletion {
	always ( all i: Internship, c: Company |
			i in c.offers implies
			always i in c.offers)
}

////////////////////// LOGIC FACTS

// in order to participate in an internship, there must 
//have been an application
// and the application must have been approved
fact ParticipationRequiresApprovedApplication {
	always ( all s: Student, i: Internship |
		    s in i.participants implies 
		      some a: Application | 
		        a in s.applies and 
		        a.refers = i and 
		        a.status = APPROVED)
}

// it's not possible to apply twice to the same internship
fact NoDuplicateApplications {
	always ( all s: Student, i: Internship |
		    lone a: Application | 
		      a in s.applies and 
		      a.refers = i)
}

// different companies offer different internships
fact NoSameInternship {
	always (all c1, c2: Company | c1 != c2 implies
			#(c1.offers & c2.offers) = 0)
}

// students can only provide feedback about 
// internships they have participated in
fact StudentFeedbackIfParticipant {
  	always ( all f: StudentFeedback, s: Student |
	    f in s.submits implies
	      s in f.about.participants)
}

// companies can only provide feedback about 
// students that participated in one of their internships
fact CompanyFeedbackIfParticipant {
  	always ( all f: CompanyFeedback, c: Company |
	    f in c.submits implies
	      some i: Internship |
	        i in c.offers and
	        f.about in i.participants)
}

// an approved application can't change its status anymore
fact StatusNotPendingDoesntChange {
	always ( all a: Application |
			(a.status = APPROVED or a.status = REJECTED)
			implies
			always a.status = a.status')
}

////////////////////// PREDICATES

pred ApplicationApproved [a: Application] {
  	a.status = PENDING
	a.status' = APPROVED
}

pred ApplicationRejected [a: Application] {
  	a.status = PENDING
  	a.status' = REJECTED
}
//run ApplicationRejected for 3

pred CompanyCreatesInternship {
	some c: Company | #c.offers' > #c.offers
	some a1, a2: Application | a1 != a2
	after all a: Application | a.status = PENDING
}
//run CompanyCreatesInternship

pred StudentAppliesToInternship {
	some s: Student | #s.applies' > #s.applies and
		some a1, a2: Application |
			a1 in s.applies and a2 in s.applies and
			// application is rejected
			eventually ApplicationRejected[a2] and
			// application approved
			eventually ApplicationApproved[a1] and
			// student is selected for the internship
			eventually s in a1.refers.participants
}
//run StudentAppliesToInternship

pred CompanyWritesFeedback {
	some c: Company | #c.submits' > #c.submits and 
		c.offers = c.offers'
}
//run CompanyWritesFeedback for 2

pred StudentWritesFeedback {
	some s: Student | #s.submits' > #s.submits and 
		s.applies = s.applies'
}
//run StudentWritesFeedback for 2

pred CompanyWritesComment {
	some c: Company | #c.writes' > #c.writes and 
		c.offers = c.offers'
}
//run CompanyWritesComment for 2

pred StudentWritesComment {
	some s: Student | #s.writes' > #s.writes and 
		s.applies = s.applies'
}
//run StudentWritesComment for 2

////////////////////// ASSERTIONS

assert NoStudentLeaveInternship {
	always ( no s: Student | some i: Internship |
			s in i.participants and s not in i.participants')
}
//check NoStudentLeaveInternship for 10 steps

assert ParticipantsIffApproved {
	always ( no s: Student, i: Internship |
		s in i.participants and no a: Application |
			a in s.applies and a.refers = i and a.status = APPROVED)
}
//check ParticipantsIffApproved

assert NoChangeInternshipOwner {
	always (no i: Internship, c: Company |
			i in c.offers and eventually i not in c.offers')
}
//check NoChangeInternshipOwner for 10 steps

assert NoChangeApplicaitonOwner {
	always ( all a: Application | no disj s1, s2: Student |
			a in s1.applies and a in s2.applies')
}
//check NoChangeApplicaitonOwner

assert FeedbackFromStudentParticipant {
	always ( no s: Student, sf: StudentFeedback, i: Internship |
		sf.about = i and sf in s.submits and s not in i.participants)
}
//check FeedbackFromStudentParticipant

assert FeedbackOnStudentParticipant {
	always ( no c: Company, cf: CompanyFeedback, s: Student |
		cf.about = s and cf in c.submits and no i: Internship |
		 	i in c.offers and s in i.participants)
}
//check FeedbackOnStudentParticipant

assert StudentCommentOnRelativeFeedback {
	always( no sc: StudentComment, cf: CompanyFeedback, c: Company |
		sc.about = cf and cf in c.submits and no i: Internship |
			cf.about in i.participants and i in c.offers)
}
//check StudentCommentOnRelativeFeedback

assert CompanyCommentOnRelativeFeedback {
	always ( no cc: CompanyComment, sf: StudentFeedback, s: Student |
		cc.about = sf and sf in s.submits and 
		// sf.about is the internship
		s not in sf.about.participants
}
//check CompanyCommentOnRelativeFeedback
