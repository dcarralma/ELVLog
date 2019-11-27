package reasoner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.SWRLArgument;
import org.semanticweb.owlapi.model.SWRLAtom;
import org.semanticweb.vlog4j.core.model.api.PositiveLiteral;
import org.semanticweb.vlog4j.core.model.api.Term;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;

public class VAtom {

	private String predicate;
	private ArrayList<String> terms;

	public VAtom(OWLClass p, OWLIndividual t) {
		this(p.toString(), t.toString());
	}

	public VAtom(OWLClass p, String t) {
		this(p.toString(), t);
	}

	public VAtom(String p, OWLIndividual t) {
		this(p, t.toString());
	}

	public VAtom(String p, String t) {
		if (p.equals("owl:Thing") || p.equals("<owl:Thing>"))
			predicate = SWURIs.owlThing;
		else if (p.equals("owl:Nothing") || p.equals("<owl:Nothing>"))
			predicate = SWURIs.owlNothing;
		else
			predicate = p;
		terms = new ArrayList<String>();
		terms.add(t);
	}

	public VAtom(OWLObjectProperty p, OWLIndividual t1, OWLIndividual t2) {
		this(p.toString(), t1.toString(), t2.toString());
	}

	public VAtom(OWLObjectProperty p, String t1, OWLIndividual t2) {
		this(p.toString(), t1, t2.toString());
	}

	public VAtom(OWLObjectProperty p, String t1, String t2) {
		this(p.toString(), t1, t2);
	}

	public VAtom(String p, OWLIndividual t1, OWLIndividual t2) {
		this(p, t1.toString(), t2.toString());
	}

	public VAtom(String p, String t1, String t2) {
		predicate = p;
		terms = new ArrayList<String>();
		terms.add(t1);
		terms.add(t2);
	}

	public VAtom(SWRLAtom safeBodyAtom, HashMap<SWRLArgument, String> safeVarToXVarMap) {
		predicate = safeBodyAtom.getPredicate().toString();
		terms = new ArrayList<String>();
		for (SWRLArgument argument : safeBodyAtom.getAllArguments()) {
			if (argument.toString().contains("Variable"))
				terms.add(safeVarToXVarMap.get(argument));
			else
				System.out.println(
						"WARNING!!! Argument which is not a varaible found at VAtom at VAtom: unimplemented functionality");
		}

		if (terms.size() != 1 && terms.size() != 2)
			System.out.println(
					"WARNING!!! Illegal VAtom instantiated by VAtom(SWRLAtom safeBodyAtom, HashMap<SWRLArgument, String> safeVarToXVarMap): invalid number of terms");
	}

	public VAtom(VAtom a) {
		predicate = new String(a.getPredicate());
		terms = new ArrayList<String>();
		for (String term : a.getTerms())
			terms.add(new String(term));
	}

	public String getPredicate() {
		return predicate;
	}

	public ArrayList<String> getTerms() {
		return terms;
	}

	public PositiveLiteral toVLogAtom() {
		List<Term> arguments = new ArrayList<Term>();
		for (String term : terms)
			if (term.startsWith("V"))
				arguments.add(Expressions.makeUniversalVariable(term));
			else
				arguments.add(Expressions.makeAbstractConstant(term));

		return Expressions.makePositiveLiteral(Expressions.makePredicate(predicate, terms.size()), arguments);
	}

	String toOxAtom() {
		String oxFormattedAtom = predicate + "(";
		for (String term : terms)
			oxFormattedAtom += term + ", ";
		return oxFormattedAtom.substring(0, oxFormattedAtom.length() - 2) + ")";
	}

	// public GroundTerm[] toGroundTermFact() {
	// GroundTerm[] oxFact = new GroundTerm[3];
	// switch (terms.size()) {
	// case 1:
	// oxFact[0] = Individual.create((terms.get(0)).replace("<", "").replace(">",
	// ""));
	// oxFact[1] = Individual.RDF_TYPE;
	// oxFact[2] = Individual.create(predicate.replace("<", "").replace(">", ""));
	// return oxFact;
	// case 2:
	// oxFact[0] = Individual.create((terms.get(0)).replace("<", "").replace(">",
	// ""));
	// oxFact[1] = Individual.create((predicate).replace("<", "").replace(">", ""));
	// oxFact[2] = Individual.create((terms.get(1)).replace("<", "").replace(">",
	// ""));
	// return oxFact;
	// default:
	// System.out.println(this.toString());
	// System.out.println("WARNING!!! Non-valid fact at toOxFact at OxAtom.java.");
	// return null;
	// }
	// }
}
