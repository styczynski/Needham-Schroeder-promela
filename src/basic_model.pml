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

/* Basic data types */
mtype:DataType = {A, B, C, X, Y, ANY};

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
	chExchange ! A, X, A, B;
	chExchange ? A, X, g1, A;
	chConfirm ! A, g1, B;
	atomic {
		processASuccess = 1;
	}
}

/* Acceptor of connection */
proctype ProcessB() {
	mtype:DataType g2, g3;
	chExchange ? B, g2, g3, B;
	chExchange ! B, g2, Y, g3;
	chConfirm ? B, Y, B;
	atomic {
		processBSuccess = 1;
	}
}

/* MITM Agent */
proctype ProcessC() {
	mtype:DataType b, c, d;
	do
		:: (processASuccess && processBSuccess) -> break
		:: else -> if
			/* Behave like a transparent proxy delivering messages to destinations */
			:: chExchange ? A, b, c, d -> chExchange ! B, b, c, d
			:: chExchange ? B, b, c, d -> chExchange ! A, b, c, d
			:: chConfirm ? A, b, c -> chConfirm ! B, b, c
			:: chConfirm ? B, b, c -> chConfirm ! A, b, c
		fi;
	od;
}

init {
	run ProcessA();
	run ProcessB();
	run ProcessC();
}
