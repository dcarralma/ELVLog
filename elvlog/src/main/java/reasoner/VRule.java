package reasoner;

import java.util.ArrayList;

public class VRule {

	private ArrayList<VAtom> head;
	private ArrayList<VAtom> body;

	public VRule(VAtom h, VAtom b) {
		head = new ArrayList<VAtom>();
		head.add(h);
		body = new ArrayList<VAtom>();
		body.add(b);
	}

	public VRule(VAtom h, VAtom b1, VAtom b2) {
		head = new ArrayList<VAtom>();
		head.add(h);
		body = new ArrayList<VAtom>();
		body.add(b1);
		body.add(b2);
	}

	public VRule(VAtom h, VAtom b1, VAtom b2, VAtom b3) {
		head = new ArrayList<VAtom>();
		head.add(h);
		body = new ArrayList<VAtom>();
		body.add(b1);
		body.add(b2);
		body.add(b3);
	}

	public VRule(VAtom h, ArrayList<VAtom> b) {
		head = new ArrayList<VAtom>();
		head.add(h);
		body = new ArrayList<VAtom>();
		for (VAtom bodyAtom : b)
			body.add(new VAtom(bodyAtom));
	}

	public VRule(ArrayList<VAtom> h, VAtom b) {
		head = new ArrayList<VAtom>();
		for (VAtom headAtom : h)
			head.add(new VAtom(headAtom));
		body = new ArrayList<VAtom>();
		body.add(new VAtom(b));
	}

	public VRule(ArrayList<VAtom> h, ArrayList<VAtom> b) {
		head = new ArrayList<VAtom>();
		for (VAtom headAtom : h)
			head.add(new VAtom(headAtom));
		body = new ArrayList<VAtom>();
		for (VAtom bodyAtom : b)
			body.add(new VAtom(bodyAtom));
	}

	public ArrayList<VAtom> getHead() {
		return head;
	}

	public ArrayList<VAtom> getBody() {
		return body;
	}

	public String toOxRules() {

		String ruleBody = new String("");
		for (VAtom bodyAtom : body)
			ruleBody += bodyAtom.toOxAtom() + ", ";
		ruleBody = ruleBody.substring(0, ruleBody.length() - 2);

		String oxRule = new String("");
		for (VAtom headAtom : head)
			oxRule += headAtom.toOxAtom() + " :-  " + ruleBody + ".";

		return oxRule;
	}
}
