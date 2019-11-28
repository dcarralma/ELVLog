package reasoner;

import org.semanticweb.vlog4j.core.model.api.Predicate;
import org.semanticweb.vlog4j.core.model.implementation.Expressions;

public class SpecialPreds {
	public static String owlThingPredName = "<http://www.w3.org/2002/07/owl#Thing>";
	public static String owlNothingPredName = "<http://www.w3.org/2002/07/owl#Nothing>";
	public static String owlSameAsPredName = "<http://www.w3.org/2002/07/owl#sameAs>";
	public static String rdfTypePredName = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
	public static String namedPredName = "<http://NamedIndividual>";
	public static String triplePredName = "<http://triple>";
	public static Predicate triplePred = Expressions.makePredicate(triplePredName, 3);
}
