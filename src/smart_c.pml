/*
 * Promela basic model for asymmetric key exchange protocol
 * MIT License
 *
 * Piotr Styczynski
 * 24-04-2019
 */
 
/* Flags to indicate if the key exchange was successful */
bit processASuccess = 0;
bit processBSuccess = 0;

/* Knowledge state of an agent */
bit know_X = 0;
bit know_Y = 0;
bit know_XYA = 0;
bit know_XAB = 0;
bit know_YB = 0;

/*
 * Basic data types
 *  - NA represents data not known by the agent
 *  - ANY represents data known by the agent, but such that its exact value can by anything
 */
mtype:DataType = {A, B, C, X, Y, ANY, NA};

/*
 * Channel for 3-compounds messages
 * <source/dest> <data1> <data2> <pubkey_used_for_enryption>
 */
chan chExchange = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType, mtype:DataType
};

/*
 * Channel for 2-compounds messages
 * <source/dest> <data> <pubkey_used_for_enryption>
 */
chan chConfirm = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType
};

/* Initiator of connection */
proctype ProcessA() {
	mtype:DataType g1;
	atomic {
		chExchange ! A, X, A, B;
	}
	atomic {
		chExchange ? A, X, g1, A;
		chConfirm ! A, g1, B;
	}
	atomic {
		processASuccess = 1;
	}
}

/* Acceptor of connection */
proctype ProcessB() {
	mtype:DataType g2, g3;
	atomic {
		chExchange ? B, g2, g3, B;
		chExchange ! B, g2, Y, g3;
	}
	atomic {
		chConfirm ? B, Y, B;
	}
	atomic {
		processBSuccess = 1;
	}
}

/*
 * Helper macros to set knowledge flags
 */
#define learn1(data1) if \
		:: (data1 == X)-> know_X = 1 \
		:: (data1 == Y)-> know_Y = 1 \
		:: else skip \
	fi;

#define learn2(data1,data2) if \
		:: (data1 == Y && data2 == B)-> know_YB = 1 \
		:: else skip \
	fi;

#define learn3(data1,data2,data3) if \
		:: (data1 == X && data2 == A && data3 == B) -> know_XAB = 1 \
		:: (data1 == X && data2 == Y && data3 == A) -> know_XYA = 1 \
		:: else skip \
	fi;

/* MITM Agent */
proctype ProcessC() {

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
		run ProcessA();
		run ProcessB();
		run ProcessC();
	}
}
