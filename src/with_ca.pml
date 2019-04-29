bit processASuccess = 0;
bit processBSuccess = 0;

bit know_X = 0;
bit know_Y = 0;
bit know_XYA = 0;
bit know_XAB = 0;
bit know_YB = 0;

mtype:DataType = {A, B, C, X, Y, ANY, NA};
mtype:CAName = {CA_A, CA_B};

chan chCA = [1] of {
	mtype:CAName, chan
};

chan chExchange = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType, mtype:DataType
};

chan chConfirm = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType
};

proctype ProcessCA() {
	mtype:CAName chReqIn;
	chan c;
	do
		:: (processASuccess && processBSuccess) -> break;
		:: else ->
			chCA ? chReqIn, c;
			if
				:: (chReqIn == CA_A) -> c ! A;
				:: (chReqIn == CA_B) -> c ! B;
			fi
	od
}

proctype ProcessA() {
	chan chCAtoA = [1] of { mtype:DataType };
	mtype:DataType pubB;
	
	mtype:DataType g1;
	atomic {
		chCA ! CA_B, chCAtoA;
		chCAtoA ? pubB;
		chExchange ! A, X, A, pubB;
	}
	atomic {
		chExchange ? A, X, g1, A;
		chConfirm ! A, g1, pubB;
	}
	atomic {
		processASuccess = 1;
	}
}

proctype ProcessB() {
	chan chCAtoB = [1] of { mtype:DataType };
	mtype:DataType pubA;
	
	mtype:DataType g2, g3;
	atomic {
		chExchange ? B, g2, g3, B;
		
		chCA ! CA_A, chCAtoB;
		chCAtoB ? pubA;
		chExchange ! B, g2, Y, pubA;
	}
	atomic {
		chConfirm ? B, Y, B;
	}
	atomic {
		processBSuccess = 1;
	}
}

#define learn1(data1) if \
		:: (data1 == X)-> know_X = 1 \
		:: (data1 == Y)-> know_Y = 1 \
		:: else skip \
	fi;

#define learn2(data1,data2) if \
		:: (data1 == Y && data2 == pubB)-> know_YB = 1 \
		:: else skip \
	fi;

#define learn3(data1,data2,data3) if \
		:: (data1 == X && data2 == A && data3 == pubB) -> know_XAB = 1 \
		:: (data1 == X && data2 == Y && data3 == pubA) -> know_XYA = 1 \
		:: else skip \
	fi;

proctype ProcessC() {

	chan chCAtoC = [1] of { mtype:DataType };
	mtype:DataType pubA;
	mtype:DataType pubB;
	
	chCA ! CA_A, chCAtoC;
	chCAtoC ? pubA;
	
	chCA ! CA_B, chCAtoC;
	chCAtoC ? pubB;
	

	mtype:DataType data1 = 0, data2 = 0, data3 = 0;
	do
		:: (processASuccess && processBSuccess) -> break;
		:: else ->
			do
			
				:: chExchange ! ((know_X || know_XAB) -> B : NA), X, A, B
				:: chExchange ! (know_X -> B : NA), X, B, B
				:: chExchange ! (know_X -> B : NA), X, C, B
				:: chExchange ! (know_Y -> B : NA), Y, A, B
				:: chExchange ! (know_Y -> B : NA), Y, B, B
				:: chExchange ! (know_Y -> B : NA), Y, C, B
				:: chExchange ! B, ANY, A, B
				:: chExchange ! B, ANY, B, B
				:: chExchange ! B, ANY, C, B
				:: chExchange ! (know_X -> A : NA), X, A, A
				:: chExchange ! (know_X -> A : NA), X, B, A
				:: chExchange ! (know_X -> A : NA), X, C, A
				:: chExchange ! B, A, A, B
				:: chExchange ! B, A, B, B
				:: chExchange ! B, A, C, B
				:: chExchange ! B, B, A, B
				:: chExchange ! B, B, B, B
				:: chExchange ! B, B, C, B
				:: chExchange ! B, C, A, B
				:: chExchange ! B, C, B, B
				:: chExchange ! B, C, C, B
				:: chConfirm ! ((know_YB || know_Y) -> B : NA), Y, B
				:: chConfirm ! ((know_YB || know_Y) -> B : NA), Y, B
				:: chExchange ! (know_X -> A : NA), X, X, A
				:: chExchange ! (((know_X && know_Y) || know_XYA) -> A : NA), X, Y, A
				:: chExchange ! (know_X -> A : NA), X, ANY, A
				:: d_step {
					chExchange ? _, data1, data2, data3; if
						:: (data3 == C)-> learn1(data1); learn1(data2)
						:: else learn3(data1,data2,data3)
					fi;
					data1 = 0; data2 = 0; data3 = 0;
				}
				:: d_step {
					chConfirm ? _, data1, data2; if
						:: (data2 == C)-> learn1(data1)
						:: else learn2(data1,data2)
					fi;
					data1 = 0; data2 = 0;
				}
			od
	od
}

init {
	atomic {
		run ProcessCA();
		run ProcessA();
		run ProcessB();
		run ProcessC();
	}
}
