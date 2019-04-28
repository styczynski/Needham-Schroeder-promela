#define MESSAGE_LEN 2

mtype:KeyType = { KPUB_A, KPUB_B, KPRIV_A, KPRIV_B, KEMPTY };
mtype:MessageType = { MESSAGE_PLAIN, MESSAGE_ENCODED };
typedef Message {
	byte data[MESSAGE_LEN];
	chan c;
	mtype:KeyType key = KEMPTY;
};

inline randomMessageContent(out, cntName) {
	atomic {
		for (cntName : 0 .. MESSAGE_LEN-1) {
			if
				:: out.data[cntName] = 10
				:: out.data[cntName] = 20
				:: out.data[cntName] = 30
				:: out.data[cntName] = 40
				:: out.data[cntName] = 50
				:: out.data[cntName] = 60
				:: out.data[cntName] = 70
				:: out.data[cntName] = 80
				:: out.data[cntName] = 90
				:: out.data[cntName] = 100
			fi
		}
	}
}

inline messageEncode(cntName, out, X, k) {
	atomic {
		for (cntName : 0 .. MESSAGE_LEN-1) {
			out.data[cntName] = X.data[cntName]
		}
		out.key = k;
		out.c = X.c;
	}
}

inline messageDecode(cntName, out, X, l) {
	atomic {
		for (cntName : 0 .. MESSAGE_LEN-1) {
			out.data[cntName] = X.data[cntName]
		}
		out.c = X.c;
		if
			:: (X.key != KEMPTY && X.key == KPUB_A && l == KPRIV_A) -> out.key = KEMPTY
			:: (X.key != KEMPTY && X.key == KPUB_B && l == KPRIV_B) -> out.key = KEMPTY
			:: (X.key != KEMPTY && X.key == KPUB_A && l != KPRIV_A) -> assert(false)
			:: (X.key != KEMPTY && X.key == KPUB_B && l != KPRIV_B) -> assert(false)
			:: else -> out.key = X.key
		fi
	}
}

inline sendEncryptedMessage(channel, messageToSend, keyVal, helperCnt, helperMessageBuf) {
	messageEncode(helperCnt, helperMessageBuf, messageToSend, keyVal);
	channel!helperMessageBuf.key,helperMessageBuf
}

inline rcvEncryptedMessage(channel, messageToWriteTo, keyVal, helperCnt, helperMessageBuf) {
	channel?_,helperMessageBuf;
	messageDecode(helperCnt, messageToWriteTo, helperMessageBuf, keyVal);
}

mtype:certAgencyDomain = { requestCertA, requestCertB }
chan certAgencyIn = [16] of {
	mtype:certAgencyDomain, chan
}

proctype CertAgency() {
	int i;
	for (i : 1 .. 2) {
		mtype:certAgencyDomain msgDomain;
		chan msgReturnChannel;
		
		certAgencyIn?msgDomain,msgReturnChannel;
		if
			:: (msgDomain == requestCertA) -> msgReturnChannel!KPUB_A
			:: (msgDomain == requestCertB) -> msgReturnChannel!KPUB_B
		fi
	}
}

chan AtoB = [16] of { mtype:KeyType, Message }

proctype A() {

	local chan BtoA = [16] of { mtype:KeyType, Message }
	local chan promiseCertB = [1] of { mtype:KeyType };
	local mtype:KeyType certB;
	local int helperCntA;
	local Message helperMessageBufA;
	
	certAgencyIn!requestCertB,promiseCertB;
	promiseCertB?certB;
	
	local Message messageXASend;
	randomMessageContent(messageXASend, helperCntA);
	messageXASend.key = KEMPTY;
	messageXASend.c = BtoA;
	sendEncryptedMessage(AtoB, messageXASend, certB, helperCntA, helperMessageBufA);
	
	local Message messageXYRecv;
	rcvEncryptedMessage(BtoA, messageXYRecv, KPRIV_A, helperCntA, helperMessageBufA);
	
	assert(messageXASend.data[0] == messageXYRecv.data[0]);
	
	local Message messageYSend;
	randomMessageContent(messageYSend, helperCntA);
	messageYSend.data[0] = messageXYRecv.data[1];
	
	messageYSend.key = KEMPTY;
	messageYSend.c = messageXYRecv.c;
	sendEncryptedMessage(AtoB, messageYSend, certB, helperCntA, helperMessageBufA);
	
	printf("A got key Y={c=%d, key=%e}\n", messageXYRecv.data[1], messageXYRecv.key);
}

proctype B() {
	chan BtoARet;
	chan promiseCertA = [1] of { mtype:KeyType };
	mtype:KeyType certA;
	local int helperCntB;
	local Message helperMessageBufB;
	
	local Message messageXARecv;
	rcvEncryptedMessage(AtoB, messageXARecv, KPRIV_B, helperCntB, helperMessageBufB);
	BtoARet = messageXARecv.c;
	
	certAgencyIn!requestCertA,promiseCertA;
	promiseCertA?certA;
	
	local Message messageXYSend;
	randomMessageContent(messageXYSend, helperCntB);
	messageXYSend.data[0] = messageXARecv.data[0];
	messageXYSend.key = KEMPTY;
	sendEncryptedMessage(BtoARet, messageXYSend, certA, helperCntB, helperMessageBufB);
	
	local Message messageYRecv;
	rcvEncryptedMessage(AtoB, messageYRecv, KPRIV_B, helperCntB, helperMessageBufB);
	
	assert(messageYRecv.data[0] == messageXYSend.data[1]);
	
	printf("B got key Y={c=%d, key=%e}\n", messageYRecv.data[0], messageYRecv.key);
}

init {
	run A(); run B(); run CertAgency();
}