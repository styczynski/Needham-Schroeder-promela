bit processASuccess = 0;
bit processBSuccess = 0;

mtype:DataType = {A, B, C, X, Y, ANY};

chan chExchange = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType, mtype:DataType
};

chan chConfirm = [0] of {
	mtype:DataType, mtype:DataType, mtype:DataType
};

proctype ProcessA() {
	mtype:DataType g1;
	chExchange ! A, X, A, B;
	chExchange ? A, X, g1, A;
	chConfirm ! A, g1, B;
	atomic {
		processASuccess = 1;
	}
}

proctype ProcessB() {
	mtype:DataType g2, g3;
	chExchange ? B, g2, g3, B;
	chExchange ! B, g2, Y, g3;
	chConfirm ? B, Y, B;
	atomic {
		processBSuccess = 1;
	}
}

proctype ProcessC() {
	mtype:DataType b, c, d;
	do
		:: (processASuccess && processBSuccess) -> break
		:: else -> if
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
