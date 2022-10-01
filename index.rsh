'reach 0.1';

const [isOutcome, A_WINS, DRAW, B_WINS] = makeEnum(3);

const winner = (Hand1, Hand2, Guess1, Guess2) => {
  const total = Hand1 + Hand2;
  if ((Guess1 == Guess2) || ((Guess1 != total) && (Guess2 != total))) {
    return DRAW;
  }
  else if (Guess1 == total) {
    return A_WINS;
  }
  else {
    return B_WINS;
  }
}

forall(UInt,handAlice =>
  forall(UInt,handBob =>
    forall(UInt,guessAlice =>
      forall(UInt,guessBob =>
      assert(isOutcome(winner(handAlice,handBob,guessAlice,guessBob)))))))

forall(UInt,a =>
  forall(UInt,b =>
    forall(UInt,c =>
      assert((winner(a,b,c,c)) == DRAW))))

const commonInteract = {
  ...hasRandom,
  getHand: Fun([], UInt),
  getGuess: Fun([], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {

  const Alice = Participant('Alice', {
    ...commonInteract,
    wager: UInt,
    deadline: UInt,
  });

  const Bob = Participant('Bob', {
    ...commonInteract,
    acceptWager: Fun([UInt], Null),
  });

  init();

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    })
  }

  Alice.only(() => {
    const amount = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });

  Alice.publish(amount, deadline)
    .pay(amount)
  commit();

  Bob.only(() => {
    interact.acceptWager(amount);
  });
  Bob.pay(amount)
    .timeout(relativeTime(deadline), () => closeTo(Alice,informTimeout));
  
  var outcome = DRAW;
  invariant(balance() == 2 * amount);
  while (outcome == DRAW){
    commit();

    Alice.only(() => {
      const _handAlice = interact.getHand();
      const _guessAlice = interact.getGuess();
      const [_commitAlice1,_saltAlice1] = makeCommitment(interact,_handAlice);
      const [_commitAlice2,_saltAlice2] = makeCommitment(interact,_guessAlice);
      const commitAlice1 = declassify(_commitAlice1);
      const commitAlice2 = declassify(_commitAlice2);
    })

    Alice.publish(commitAlice1,commitAlice2)
      .timeout(relativeTime(deadline), () => closeTo(Bob,informTimeout));

    commit();

    unknowable(Bob, Alice(_handAlice,_guessAlice,_saltAlice1,_saltAlice2));

    Bob.only(() => {
      const handBob = declassify(interact.getHand());
      const guessBob = declassify(interact.getGuess());
    })
    Bob.publish(handBob,guessBob)
      .timeout(relativeTime(deadline), () => closeTo(Alice,informTimeout));
      
    commit();

    Alice.only(() => {
        const saltAlice1 = declassify(_saltAlice1);
        const saltAlice2 = declassify(_saltAlice2);
        const handAlice = declassify(_handAlice);
        const guessAlice = declassify(_guessAlice);
    });
    Alice.publish(saltAlice1, saltAlice2, handAlice, guessAlice)
      .timeout(relativeTime(deadline), ()=> closeTo(Bob, informTimeout));

    checkCommitment(commitAlice1, saltAlice1, handAlice);
    checkCommitment(commitAlice2, saltAlice2, guessAlice);

    outcome = winner(handAlice, handBob, guessAlice, guessBob);
    continue;
  }

  assert (outcome != DRAW);
  transfer(2 * amount).to(outcome == A_WINS ? Alice : Bob);
  commit();

  each([Alice, Bob], () => {
    interact.seeOutcome(outcome);
  })

  exit();
});